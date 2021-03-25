{-# Language GADTs #-}
{-# Language RecordWildCards #-}
{-# Language FlexibleContexts #-}
{-# Language LambdaCase #-}
{-# Language BlockArguments #-}
{-# Language RankNTypes #-}
{-# Language TemplateHaskell #-}
{-# Language QuasiQuotes #-}
{-# Language TypeOperators #-}
{-# Language DataKinds #-}
{-# Language ViewPatterns #-}
{-# Language ImportQualifiedPost #-}
{-# Language ScopedTypeVariables #-}
{-# Language KindSignatures #-}
{-# Options_GHC -Wno-unused-foralls #-}
module Verifier.SAW.Heapster.TypeChecker (
  -- * Checker type
  Tc, startTc,

  -- * Checker errors
  TypeError(..),

  tcFunPerm,
  tcCtx,
  tcType,
  tcExpr,
  tcValPerm,
  inParsedCtxM,
  tcAtomicPerms,
  tcValPermInCtx,
  tcSortedMbValuePerms,
  ) where

import Control.Monad
import Data.Functor.Product
import Data.Functor.Constant
import GHC.TypeLits (Nat, KnownNat)
import GHC.Natural

import Data.Binding.Hobbits
import Data.Binding.Hobbits.MonadBind

import Prettyprinter hiding (comma, space)

import Data.Type.RList qualified as RL
import Data.Parameterized.Some (Some(Some), mapSome)
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.BoolRepr (BoolRepr(TrueRepr))

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Bytes

import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Located
import Verifier.SAW.Heapster.UntypedAST
import Verifier.SAW.Heapster.ParsedCtx

----------------------------------------------------------------------
-- * Type-checking environment
----------------------------------------------------------------------

data TcEnv = TcEnv {
  tcEnvExprVars :: [(String, TypedName)],
  tcEnvPermEnv :: PermEnv
}

----------------------------------------------------------------------
-- * Type-checking type
----------------------------------------------------------------------

data TypeError = TypeError Pos String
  deriving Show

$(mkNuMatching [t| TypeError |])

instance Closable TypeError where
  toClosed = unsafeClose
instance Liftable TypeError where
  mbLift = unClosed . mbLift . fmap toClosed

newtype Tc a = Tc { runTc :: TcEnv -> Either TypeError a }

startTc :: Tc a -> PermEnv -> Either TypeError a
startTc tc env = runTc tc (TcEnv [] env)

instance Functor Tc where
  fmap = liftM

instance Applicative Tc where
  pure x = Tc \_ -> Right x
  (<*>) = ap

instance Monad Tc where
  Tc f >>= g = Tc \env ->
    do x <- f env
       runTc (g x) env

instance MonadBind Tc where
  mbM m = Tc \env ->
    case fmap (`runTc` env) m of
      [nuP| Left e  |] -> Left (mbLift e)
      [nuP| Right x |] -> Right x
      _ -> error "panic: MonadBind.Tc"

tcLocal :: (TcEnv -> TcEnv) -> Tc a -> Tc a
tcLocal f (Tc k) = Tc (k . f)

tcAsk :: Tc TcEnv
tcAsk = Tc Right

tcError :: Pos -> String -> Tc a
tcError p err = Tc (\_ -> Left (TypeError p err))

withPositive ::
  Pos ->
  String ->
  Natural ->
  (forall w. (1 <= w, KnownNat w) => NatRepr w -> Tc a) ->
  Tc a
withPositive p err n k =
  case someNatGeq1 n of
    Nothing -> tcError p err
    Just (Some (Pair w LeqProof)) -> withKnownNat w (k w)

----------------------------------------------------------------------
-- * Casting
----------------------------------------------------------------------

tcCastTyped :: Pos -> TypeRepr a -> Typed f b -> Tc (f a)
tcCastTyped _ tp (Typed tp' f)
  | Just Refl <- testEquality tp tp' = pure f
tcCastTyped p tp (Typed tp' _) =
  tcError p ("Expected type " ++ show tp ++ ", got type " ++ show tp')

----------------------------------------------------------------------
-- * Extending variable environment
----------------------------------------------------------------------

withExprVar :: String -> TypeRepr tp -> ExprVar tp -> Tc a -> Tc a
withExprVar str tp x = tcLocal \env ->
  env { tcEnvExprVars = (str, Some (Typed tp x)) : tcEnvExprVars env }

-- | Run a parsing computation in a context extended with 0 or more expression
-- variables
withExprVars ::
  RAssign (Constant String) ctx ->
  CruCtx ctx ->
  RAssign Name ctx ->
  Tc a ->
  Tc a
withExprVars MNil                CruCtxNil           MNil       m = m
withExprVars (xs :>: Constant x) (CruCtxCons ctx tp) (ns :>: n) m = withExprVars xs ctx ns (withExprVar x tp n m)

----------------------------------------------------------------------
-- * Checking Types
----------------------------------------------------------------------

tcType :: AstType -> Tc (Some TypeRepr)
tcType t = mapSome unKnownReprObj <$> tcTypeKnown t

tcTypeKnown :: AstType -> Tc (Some (KnownReprObj TypeRepr))
tcTypeKnown t =
  case t of
    TyUnit          {} -> pure (Some (mkKnownReprObj UnitRepr))
    TyBool          {} -> pure (Some (mkKnownReprObj BoolRepr))
    TyNat           {} -> pure (Some (mkKnownReprObj NatRepr))
    TyLifetime      {} -> pure (Some (mkKnownReprObj LifetimeRepr))
    TyRwModality    {} -> pure (Some (mkKnownReprObj RWModalityRepr))
    TyPermList      {} -> pure (Some (mkKnownReprObj PermListRepr))

    TyBV p n ->
      withPositive p "Zero bitvector width not allowed" n \w ->
        pure (Some (mkKnownReprObj (BVRepr w)))
    TyLlvmPtr p n ->
      withPositive p "Zero LLVM Ptr width not allowed" n \w ->
        pure (Some (mkKnownReprObj (LLVMPointerRepr w)))
    TyLlvmFrame p n ->
      withPositive p "Zero LLVM Frame width not allowed" n \w ->
        pure (Some (mkKnownReprObj (LLVMFrameRepr w)))
    TyLlvmShape p n ->
      withPositive p "Zero LLVM Shape width not allowed" n \w ->
        pure (Some (mkKnownReprObj (LLVMShapeRepr w)))
    TyLlvmBlock p n ->
      withPositive p "Zero LLVM Block width not allowed" n \w ->
        pure (Some (mkKnownReprObj (LLVMBlockRepr w)))

    TyStruct _ fs ->
      do fs1 <- traverse tcTypeKnown fs
         let fs2 = foldl structAdd (Some (mkKnownReprObj Ctx.empty)) fs1
         case fs2 of
           Some xs@KnownReprObj -> pure (Some (mkKnownReprObj (StructRepr (unKnownReprObj xs))))

    TyPerm _ x ->
      do Some tp@KnownReprObj <- tcTypeKnown x
         pure (Some (mkKnownReprObj (ValuePermRepr (unKnownReprObj tp))))

structAdd ::
  Some (KnownReprObj (Ctx.Assignment TypeRepr)) ->
  Some (KnownReprObj TypeRepr) ->
  Some (KnownReprObj (Ctx.Assignment TypeRepr))
structAdd (Some acc@KnownReprObj) (Some x@KnownReprObj) =
  Some (mkKnownReprObj (Ctx.extend (unKnownReprObj acc) (unKnownReprObj x)))

----------------------------------------------------------------------
-- * Checking Expressions
----------------------------------------------------------------------

tcVar :: TypeRepr a -> Pos -> String -> Tc (ExprVar a)
tcVar ty p name =
  do Some tn <- tcTypedName p name
     tcCastTyped p ty tn

tcTypedName :: Pos -> String -> Tc TypedName
tcTypedName p name =
  do env <- tcAsk
     case lookup name (tcEnvExprVars env) of
       Nothing -> tcError p ("Unknown variable:" ++ name)
       Just stn -> pure stn

tcKExpr :: KnownRepr TypeRepr a => AstExpr -> Tc (PermExpr a)
tcKExpr = tcExpr knownRepr

tcExpr :: TypeRepr a -> AstExpr -> Tc (PermExpr a)
tcExpr ty (ExVar p name Nothing Nothing) = PExpr_Var <$> tcVar ty p name

tcExpr tp@LLVMShapeRepr{} (ExVar p name (Just args) Nothing) =
  do env <- tcAsk
     case lookupNamedShape (tcEnvPermEnv env) name of
       Just (SomeNamedShape _ arg_ctx mb_sh)
         | Just Refl <- testEquality (mbLift (fmap exprType mb_sh)) tp ->
           do sub <- tcExprs p arg_ctx args
              pure (subst (substOfExprs sub) mb_sh)
       Just (SomeNamedShape _ _ mb_sh) ->
         tcError p $ renderDoc $ sep
         [ pretty "Named shape" <+> pretty name <+>
           pretty "is of incorrect type"
         , pretty "Expected:" <+> permPretty emptyPPInfo tp
         , pretty "Found:" <+>
           permPretty emptyPPInfo (mbLift (fmap exprType mb_sh)) ]
       Nothing -> tcError p ("Unknown shape name: " ++ name)

tcExpr tp@(ValuePermRepr sub_tp) (ExVar p name (Just args) Nothing) =
  do env <- tcAsk
     case lookupNamedPermName (tcEnvPermEnv env) name of
       Just (SomeNamedPermName npn)
         | Just Refl <- testEquality (namedPermNameType npn) sub_tp ->
           do arg_exprs <- tcExprs p (namedPermNameArgs npn) args
              pure (PExpr_ValPerm $ ValPerm_Named npn arg_exprs NoPermOffset)
       Just (SomeNamedPermName npn) ->
         tcError p $ renderDoc $ sep
         [ pretty "Named permission" <+> pretty (namedPermNameName npn) <+>
           pretty "is of incorrect type"
         , pretty "Expected:" <+> permPretty emptyPPInfo tp
         , pretty "Found:" <+> permPretty emptyPPInfo (namedPermNameType npn) ]
       Nothing -> tcError p ("Unknown shape name: " ++ name)

tcExpr _ (ExVar p _ Just{} _) = tcError p "Unexpected variable instantiation"
tcExpr _ (ExVar p _ _ Just{}) = tcError p "Unexpected variable offset"




tcExpr UnitRepr         e = tcUnit e
tcExpr NatRepr          e = tcNat e
tcExpr (BVRepr w)       e = withKnownNat w (normalizeBVExpr <$> tcBV e)
tcExpr (StructRepr fs)  e = tcStruct fs e
tcExpr LifetimeRepr     e = tcLifetimeLit e
tcExpr (LLVMPointerRepr w) e = withKnownNat w (tcLLVMPointer w e)
tcExpr FunctionHandleRepr{} e = tcError (pos e) "Expected functionhandle" -- no literals
tcExpr PermListRepr     e = tcError (pos e) "Expected permlist" -- no literals
tcExpr RWModalityRepr   e = tcRWModality e
tcExpr (ValuePermRepr t) e = permToExpr <$> tcValPerm t e
tcExpr (LLVMShapeRepr w) e = withKnownNat w (tcLLVMShape e)

tcExpr (IntrinsicRepr s _) e = tcError (pos e) ("Expected intrinsic type: " ++ show s)

-- reprs that we explicitly do not support
tcExpr BoolRepr             e = tcError (pos e) "Expected boolean"
tcExpr IntegerRepr          e = tcError (pos e) "Expected integerl"
tcExpr AnyRepr              e = tcError (pos e) "Expected any type"
tcExpr RealValRepr          e = tcError (pos e) "Expected realval"
tcExpr ComplexRealRepr      e = tcError (pos e) "Expected realval"
tcExpr CharRepr             e = tcError (pos e) "Expected char"
tcExpr RecursiveRepr     {} e = tcError (pos e) "Expected recursive-value"
tcExpr FloatRepr         {} e = tcError (pos e) "Expected float"
tcExpr IEEEFloatRepr     {} e = tcError (pos e) "Expected ieeefloat"
tcExpr StringRepr        {} e = tcError (pos e) "Expected string"
tcExpr MaybeRepr         {} e = tcError (pos e) "Expected maybe"
tcExpr VectorRepr        {} e = tcError (pos e) "Expected vector"
tcExpr VariantRepr       {} e = tcError (pos e) "Expected variant"
tcExpr ReferenceRepr     {} e = tcError (pos e) "Expected reference"
tcExpr WordMapRepr       {} e = tcError (pos e) "Expected wordmap"
tcExpr StringMapRepr     {} e = tcError (pos e) "Expected stringmap"
tcExpr SymbolicArrayRepr {} e = tcError (pos e) "Expected symbolicarray"
tcExpr SymbolicStructRepr{} e = tcError (pos e) "Expected symbolicstruct"


tcUnit :: AstExpr -> Tc (PermExpr UnitType)
tcUnit ExUnit{} = pure PExpr_Unit
tcUnit e        = tcError (pos e) "Expected unit"

tcNat :: AstExpr -> Tc (PermExpr NatType)
tcNat (ExNat _ i) = pure (PExpr_Nat i)
tcNat e           = tcError (pos e) "Expected unit"

tcBV :: (KnownNat w, 1 <= w) => AstExpr -> Tc (PermExpr (BVType w))
tcBV (ExAdd _ x y) = bvAdd <$> tcBV x <*> tcBV y
tcBV e             = tcBVFactor e

-- Note: this could be more permissive
tcBVFactor :: (KnownNat w, 1 <= w) => AstExpr -> Tc (PermExpr (BVType w))
tcBVFactor (ExNat _ i) = pure (bvInt (fromIntegral i))
tcBVFactor (ExMul _ (ExNat _ i) (ExVar p name Nothing Nothing)) =
  do Some tn <- tcTypedName p name
     bvMult i . PExpr_Var <$> tcCastTyped p knownRepr tn
tcBVFactor (ExMul _ (ExVar p name Nothing Nothing) (ExNat _ i)) =
  do Some tn <- tcTypedName p name
     bvMult i . PExpr_Var <$> tcCastTyped p knownRepr tn
tcBVFactor (ExVar p name Nothing Nothing) =
  do Some tn <- tcTypedName p name
     PExpr_Var <$> tcCastTyped p knownRepr tn
tcBVFactor e = tcError (pos e) "Expected BV factor"

tcStruct :: CtxRepr fs -> AstExpr -> Tc (PermExpr (StructType fs))
tcStruct ts (ExStruct p es) = PExpr_Struct <$> tcExprs p (mkCruCtx ts) es
tcStruct _ e = tcError (pos e) "Expected struct"

tcExprs :: Pos -> CruCtx fs -> [AstExpr] -> Tc (PermExprs fs)
tcExprs p tys es = tcExprs' p tys (reverse es)

tcExprs' :: Pos -> CruCtx fs -> [AstExpr] -> Tc (PermExprs fs)
tcExprs' _ CruCtxNil [] = pure PExprs_Nil
tcExprs' p (CruCtxCons xs x) (y:ys) =
  do zs <- tcExprs' p xs ys
     z  <- tcExpr x y
     pure (zs :>: z)
tcExprs' p _ _ = tcError p "Bad arity"

tcValuePerms :: Pos -> RAssign TypeRepr tys -> [AstExpr] -> Tc (RAssign ValuePerm tys)
tcValuePerms p tys es = tcValuePerms' p tys (reverse es)

tcValuePerms' :: Pos -> RAssign TypeRepr tps -> [AstExpr] -> Tc (RAssign ValuePerm tps)
tcValuePerms' _ MNil [] = pure MNil
tcValuePerms' p (xs :>: x) (y:ys) =
  do zs <- tcValuePerms' p xs ys
     z  <- tcValPerm x y
     pure (zs :>: z)
tcValuePerms' p _ _ = tcError p "Bad arity"

tcRWModality :: AstExpr -> Tc (PermExpr RWModalityType)
tcRWModality ExRead {} = pure PExpr_Read
tcRWModality ExWrite{} = pure PExpr_Write
tcRWModality e         = tcError (pos e) "Expected rwmodality"

tcOptLifetime :: Maybe AstExpr -> Tc (PermExpr LifetimeType)
tcOptLifetime Nothing = pure PExpr_Always
tcOptLifetime (Just e) = tcKExpr e

tcLifetimeLit :: AstExpr -> Tc (PermExpr LifetimeType)
tcLifetimeLit ExAlways{} = pure PExpr_Always
tcLifetimeLit e          = tcError (pos e) "Expected lifetime"

tcLLVMShape :: (KnownNat w, 1 <= w) => AstExpr -> Tc (PermExpr (LLVMShapeType w))
tcLLVMShape (ExOrSh _ x y) = PExpr_OrShape <$> tcKExpr x <*> tcKExpr y
tcLLVMShape (ExExSh _ var vartype sh) =
  do Some ktp'@KnownReprObj <- tcTypeKnown vartype
     fmap PExpr_ExShape $ mbM $ nu \z ->
       withExprVar var (unKnownReprObj ktp') z (tcLLVMShape sh)
tcLLVMShape (ExSeqSh _ x y) = PExpr_SeqShape <$> tcKExpr x <*> tcKExpr y
tcLLVMShape ExEmptySh{} = pure PExpr_EmptyShape
tcLLVMShape (ExEqSh _ v) = PExpr_EqShape <$> tcKExpr v
tcLLVMShape (ExPtrSh _ maybe_l maybe_rw sh) =
  PExpr_PtrShape
  <$> traverse tcKExpr maybe_l
  <*> traverse tcKExpr maybe_rw
  <*> tcKExpr sh
tcLLVMShape (ExFieldSh _ w fld) = PExpr_FieldShape <$> tcLLVMFieldShape_ w fld
tcLLVMShape (ExArraySh _ len stride flds) =
  PExpr_ArrayShape
  <$> tcKExpr len
  <*> (Bytes . fromIntegral <$> tcNatural stride)
  <*> traverse (uncurry tcLLVMFieldShape_) flds
tcLLVMShape e = tcError (pos e) "Expected shape"

tcLLVMFieldShape_ ::
  forall w. (KnownNat w, 1 <= w) => Maybe AstExpr -> AstExpr -> Tc (LLVMFieldShape w)
tcLLVMFieldShape_ Nothing e = tcLLVMFieldShape (knownNat :: NatRepr w) e
tcLLVMFieldShape_ (Just w) e =
  do Some (Pair nr LeqProof) <- tcPositive w
     withKnownNat nr (tcLLVMFieldShape nr e)

tcLLVMFieldShape ::
  forall (w :: Nat) (v :: Nat).
  (KnownNat w, 1 <= w) =>
  NatRepr w -> AstExpr -> Tc (LLVMFieldShape v)
tcLLVMFieldShape nr e = LLVMFieldShape <$> tcValPerm (LLVMPointerRepr nr) e

tcLLVMPointer :: (KnownNat w, 1 <= w) => NatRepr w -> AstExpr -> Tc (PermExpr (LLVMPointerType w))
tcLLVMPointer _ (ExLlvmWord _ e) = PExpr_LLVMWord <$> tcKExpr e
tcLLVMPointer w (ExAdd _ (ExVar p name Nothing Nothing) off) = PExpr_LLVMOffset <$> tcVar (LLVMPointerRepr w) p name <*> tcKExpr off
tcLLVMPointer _ e = tcError (pos e) "Expected llvmpointer"

-- | Check a value permission of a known type in a given context
tcValPermInCtx :: ParsedCtx ctx -> TypeRepr a -> AstExpr -> Tc (Mb ctx (ValuePerm a))
tcValPermInCtx ctx tp = inParsedCtxM ctx . const . tcValPerm tp

tcValPerm :: TypeRepr a -> AstExpr -> Tc (ValuePerm a)
tcValPerm _  ExTrue{} = pure ValPerm_True
tcValPerm ty (ExOr _ x y) = ValPerm_Or <$> tcValPerm ty x <*> tcValPerm ty y
tcValPerm ty (ExEq _ e) = ValPerm_Eq <$> tcExpr ty e
tcValPerm ty (ExExists _ var vartype e) =
  do Some ktp'@KnownReprObj <- tcTypeKnown vartype
     fmap ValPerm_Exists $ mbM $ nu \z ->
       withExprVar var (unKnownReprObj ktp') z (tcValPerm ty e)
tcValPerm ty (ExVar p n (Just argEs) maybe_off) =
  do env <- tcEnvPermEnv <$> tcAsk
     case lookupNamedPermName env n of
       Just (SomeNamedPermName rpn)
         | Just Refl <- testEquality (namedPermNameType rpn) ty ->
           do args <- tcExprs p (namedPermNameArgs rpn) argEs
              off <- tcPermOffset ty p maybe_off
              pure (ValPerm_Named rpn args off)
       Just (SomeNamedPermName rpn) ->
         tcError p $ renderDoc $ sep
         [ pretty "Named permission" <+> pretty n <+>
           pretty "is of incorrect type"
         , pretty "Expected:" <+> permPretty emptyPPInfo ty
         , pretty "Found:" <+>
           permPretty emptyPPInfo (namedPermNameType rpn) ]
       Nothing ->
         tcError p ("Unknown named permission '" ++ n ++ "'")
tcValPerm ty (ExVar p n Nothing off) =
  ValPerm_Var <$> tcVar (ValuePermRepr ty) p n <*> tcPermOffset ty p off
tcValPerm ty e = ValPerm_Conj <$> tcAtomicPerms ty e

tcAtomicPerms :: TypeRepr a -> AstExpr -> Tc [AtomicPerm a]
tcAtomicPerms ty (ExMul _ x y) = (++) <$> tcAtomicPerms ty x <*> tcAtomicPerms ty y
tcAtomicPerms ty e = pure <$> tcAtomicPerm ty e


tcAtomicPerm :: TypeRepr a -> AstExpr -> Tc (AtomicPerm a)
tcAtomicPerm ty (ExVar p n (Just argEs) maybe_off) =
  do env <- tcEnvPermEnv <$> tcAsk
     case lookupNamedPermName env n of
       Just (SomeNamedPermName npn)
         | Just Refl <- testEquality (namedPermNameType npn) ty
         , TrueRepr <- nameIsConjRepr npn ->
             do args <- tcExprs p (namedPermNameArgs npn) argEs
                off <- tcPermOffset ty p maybe_off
                return (Perm_NamedConj npn args off)
       Just (SomeNamedPermName npn)
         | Just Refl <- testEquality (namedPermNameType npn) ty ->
         tcError p ("Non-conjoinable permission name '" ++ n
                  ++ "' used in conjunctive context")
       Just (SomeNamedPermName _) ->
         tcError p ("Permission name '" ++ n ++ "' has incorrect type")
       Nothing ->
         tcError p ("Unknown permission name '" ++ n ++ "'")

tcAtomicPerm (LLVMPointerRepr w) e = withKnownNat w (tcPointerAtomic e)
tcAtomicPerm (LLVMFrameRepr w) e = withKnownNat w (tcFrameAtomic e)
tcAtomicPerm (LLVMBlockRepr w) e = withKnownNat w (tcBlockAtomic e)
tcAtomicPerm (StructRepr tys) e = tcStructAtomic tys e
tcAtomicPerm LifetimeRepr e = tcLifetimeAtomic e
tcAtomicPerm _ e = tcError (pos e) "Expected perm"

tcPointerAtomic :: (KnownNat w, 1 <= w) => AstExpr -> Tc (AtomicPerm (LLVMPointerType w))
tcPointerAtomic (ExPtr p l rw off sz c) =
  llvmArrayFieldToAtomicPerm <$> tcArrayPerm (ArrayPerm p l rw off sz c)
tcPointerAtomic (ExArray _ x y z w) = Perm_LLVMArray <$> tcArrayAtomic x y z w
tcPointerAtomic (ExMemblock _ l rw off len sh) = Perm_LLVMBlock <$> tcMemblock l rw off len sh
tcPointerAtomic (ExFree      _ x  ) = Perm_LLVMFree <$> tcKExpr x
tcPointerAtomic (ExLlvmFunPtr _ n w f) = tcFunPtrAtomic n w f
tcPointerAtomic (ExEqual     _ x y) = Perm_BVProp <$> (BVProp_Eq   <$> tcKExpr x <*> tcKExpr y)
tcPointerAtomic (ExNotEqual  _ x y) = Perm_BVProp <$> (BVProp_Neq  <$> tcKExpr x <*> tcKExpr y)
tcPointerAtomic (ExLessThan  _ x y) = Perm_BVProp <$> (BVProp_ULt  <$> tcKExpr x <*> tcKExpr y)
tcPointerAtomic (ExLessEqual _ x y) = Perm_BVProp <$> (BVProp_ULeq <$> tcKExpr x <*> tcKExpr y)
tcPointerAtomic e = tcError (pos e) "Expected pointer perm"

tcFunPtrAtomic ::
  (KnownNat w, 1 <= w) =>
  AstExpr -> AstExpr -> AstFunPerm -> Tc (AtomicPerm (LLVMPointerType w))
tcFunPtrAtomic x y fun =
  do Some args_no            <- mkNatRepr <$> tcNatural x
     Some (Pair w' LeqProof) <- tcPositive y
     Some args               <- pure (cruCtxReplicate args_no (LLVMPointerRepr w'))
     SomeFunPerm fun_perm    <- tcFunPerm args (LLVMPointerRepr w') fun
     pure (mkPermLLVMFunPtr knownNat fun_perm)

tcMemblock ::
  (KnownNat w, 1 <= w) =>
  Maybe AstExpr ->
  AstExpr -> AstExpr -> AstExpr -> AstExpr -> Tc (LLVMBlockPerm w)
tcMemblock l rw off len sh =
  do llvmBlockLifetime <- tcOptLifetime l
     llvmBlockRW       <- tcKExpr rw
     llvmBlockOffset   <- tcKExpr off
     llvmBlockLen      <- tcKExpr len
     llvmBlockShape    <- tcKExpr sh
     pure LLVMBlockPerm{..}

tcArrayAtomic ::
  (KnownNat w, 1 <= w) => AstExpr -> AstExpr -> AstExpr -> [ArrayPerm] -> Tc (LLVMArrayPerm w)
tcArrayAtomic off len stride fields =
  LLVMArrayPerm
  <$> tcKExpr off
  <*> tcKExpr len
  <*> (Bytes . fromIntegral <$> tcNatural stride)
  <*> traverse tcArrayPerm fields
  <*> pure []

tcArrayPerm :: forall w. (KnownNat w, 1 <= w) => ArrayPerm -> Tc (LLVMArrayField w)
tcArrayPerm (ArrayPerm _ l rw off sz c) =
  do llvmFieldLifetime <- tcOptLifetime l
     llvmFieldRW <- tcExpr RWModalityRepr rw
     llvmFieldOffset <- tcKExpr off :: Tc (PermExpr (BVType w))
     Some (Pair w LeqProof) <- maybe (pure (Some (Pair (knownNat :: NatRepr w) LeqProof)))
                               tcPositive sz
     withKnownNat w do
      llvmFieldContents <- withKnownNat w (tcValPerm (LLVMPointerRepr w) c)
      pure (LLVMArrayField LLVMFieldPerm{..})

tcFrameAtomic :: (KnownNat w, 1 <= w) => AstExpr -> Tc (AtomicPerm (LLVMFrameType w))
tcFrameAtomic (ExLlvmFrame _ xs) =
  Perm_LLVMFrame <$> traverse (\(e,i) -> (,) <$> tcKExpr e <*> pure (fromIntegral i)) xs
tcFrameAtomic e = tcError (pos e) "Expected llvmframe perm"

tcStructAtomic :: CtxRepr tys -> AstExpr -> Tc (AtomicPerm (StructType tys))
tcStructAtomic tys (ExStruct p es) = Perm_Struct <$> tcValuePerms p (assignToRList tys) es
tcStructAtomic _ e = tcError (pos e) "Expected struct perm"

tcBlockAtomic :: (KnownNat w, 1 <= w) => AstExpr -> Tc (AtomicPerm (LLVMBlockType w))
tcBlockAtomic (ExShape _ e) = Perm_LLVMBlockShape <$> tcKExpr e
tcBlockAtomic e = tcError (pos e) "Expected llvmblock perm"

tcLifetimeAtomic :: AstExpr -> Tc (AtomicPerm LifetimeType)
tcLifetimeAtomic (ExLOwned _ x y) =
  do Some x' <- tcLOwnedPerms x
     Some y' <- tcLOwnedPerms y
     pure (Perm_LOwned x' y')
tcLifetimeAtomic (ExLCurrent _ l) = Perm_LCurrent <$> tcOptLifetime l
tcLifetimeAtomic e = tcError (pos e) "Expected lifetime perm"

tcLOwnedPerms :: [(Located String,AstExpr)] -> Tc (Some LOwnedPerms)
tcLOwnedPerms [] = pure (Some MNil)
tcLOwnedPerms ((Located p n,e):xs) =
  do Some (Typed tp x) <- tcTypedName p n
     perm <- tcValPerm tp e
     lop <- case varAndPermLOwnedPerm (VarAndPerm x perm) of
              Just lop -> return lop
              Nothing -> tcError (pos e) ("Not a valid lifetime ownership permission: "
                                         ++ permPrettyString emptyPPInfo perm)
     Some lops <- tcLOwnedPerms xs
     pure (Some (lops :>: lop))

tcPermOffset :: TypeRepr a -> Pos -> Maybe AstExpr -> Tc (PermOffset a)
tcPermOffset _ _ Nothing = pure NoPermOffset
tcPermOffset (LLVMPointerRepr w) _ (Just i) = withKnownNat w (LLVMPermOffset <$> tcKExpr i)
tcPermOffset _ p _ = tcError p "Unexpected offset"

tcNatural :: AstExpr -> Tc Natural
tcNatural (ExNat _ i) = pure i
tcNatural e = tcError (pos e) "Expected integer literal"

tcPositive :: AstExpr -> Tc (Some (Product NatRepr (LeqProof 1)))
tcPositive e =
  do i <- tcNatural e
     withPositive (pos e) "positive required" i \w -> pure (Some (Pair w LeqProof))

tcCtx :: [(Located String, AstType)] -> Tc (Some ParsedCtx)
tcCtx []         = pure (Some emptyParsedCtx)
tcCtx ((n,t):xs) = preconsSomeParsedCtx (locThing n) <$> tcType t <*> tcCtx xs

tcSortedValuePerms ::
  VarPermSpecs ctx -> [(Located String, AstExpr)] -> Tc (ValuePerms ctx)
tcSortedValuePerms var_specs [] = pure (varSpecsToPerms var_specs)
tcSortedValuePerms var_specs ((Located p var, x):xs) =
  do Some (Typed tp n) <- tcTypedName p var
     perm              <- tcValPerm tp x
     var_specs'        <- tcSetVarSpecs p var n perm var_specs
     tcSortedValuePerms var_specs' xs

tcSortedMbValuePerms ::
  ParsedCtx ctx -> [(Located String, AstExpr)] -> Tc (MbValuePerms ctx)
tcSortedMbValuePerms ctx perms =
  inParsedCtxM ctx \ns ->
  tcSortedValuePerms (mkVarPermSpecs ns) perms

tcFunPerm :: CruCtx args -> TypeRepr ret -> AstFunPerm -> Tc (SomeFunPerm args ret)
tcFunPerm args ret (AstFunPerm _ untyCtx ins outs) =
  do Some ghosts_ctx@(ParsedCtx _ ghosts) <- tcCtx untyCtx
     let args_ctx = mkArgsParsedCtx args
         ghosts_args_ctx = appendParsedCtx ghosts_ctx args_ctx
     perms_in  <- tcSortedMbValuePerms ghosts_args_ctx ins
     perms_out <- tcSortedMbValuePerms (consParsedCtx "ret" ret ghosts_args_ctx) outs
     pure (SomeFunPerm (FunPerm ghosts args ret perms_in perms_out))

----------------------------------------------------------------------
-- * Parsing Permission Sets and Function Permissions
----------------------------------------------------------------------

-- | Helper type for 'parseValuePerms' that represents whether a pair @x:p@ has
-- been parsed yet for a specific variable @x@ and, if so, contains that @p@
data VarPermSpec a = VarPermSpec (Name a) (Maybe (ValuePerm a))

-- | A sequence of variables @x@ and what pairs @x:p@ have been parsed so far
type VarPermSpecs = RAssign VarPermSpec

-- | Build a 'VarPermSpecs' from a list of names
mkVarPermSpecs :: RAssign Name ctx -> VarPermSpecs ctx
mkVarPermSpecs = RL.map (\n -> VarPermSpec n Nothing)

-- | Find a 'VarPermSpec' for a particular variable
findVarPermSpec :: Name (a :: CrucibleType) ->
                   VarPermSpecs ctx -> Maybe (Member ctx a)
findVarPermSpec _ MNil = Nothing
findVarPermSpec n (_ :>: VarPermSpec n' _)
  | Just Refl <- testEquality n n'
  = Just Member_Base
findVarPermSpec n (specs :>: _) = Member_Step <$> findVarPermSpec n specs

-- | Try to set the permission for a variable in a 'VarPermSpecs' list, raising
-- a parse error if the variable already has a permission or is one of the
-- expected variables
tcSetVarSpecs ::
  Pos -> String -> Name tp -> ValuePerm tp -> VarPermSpecs ctx ->
  Tc (VarPermSpecs ctx)
tcSetVarSpecs p var n perm var_specs =
  case findVarPermSpec n var_specs of
    Nothing -> tcError p ("Unknown variable: " ++ var)
    Just memb ->
      case RL.get memb var_specs of
        VarPermSpec _ Nothing ->
          pure (RL.modify memb (const (VarPermSpec n (Just perm))) var_specs)
        _ -> tcError p ("Variable " ++ var ++ " occurs more than once!")

-- | Convert a 'VarPermSpecs' sequence to a sequence of permissions, using the
-- @true@ permission for any variables without permissions
varSpecsToPerms :: VarPermSpecs ctx -> ValuePerms ctx
varSpecsToPerms MNil = ValPerms_Nil
varSpecsToPerms (var_specs :>: VarPermSpec _ (Just p)) =
  ValPerms_Cons (varSpecsToPerms var_specs) p
varSpecsToPerms (var_specs :>: VarPermSpec _ Nothing) =
  ValPerms_Cons (varSpecsToPerms var_specs) ValPerm_True

-- | Run a parsing computation inside a name-binding for expressions variables
-- given by a 'ParsedCtx'. Returning the results inside a name-binding.
inParsedCtxM ::
  NuMatching a =>
  ParsedCtx ctx -> (RAssign Name ctx -> Tc a) -> Tc (Mb ctx a)
inParsedCtxM (ParsedCtx ids tps) f =
  mbM (nuMulti (cruCtxProxies tps) \ns -> withExprVars ids tps ns (f ns))
