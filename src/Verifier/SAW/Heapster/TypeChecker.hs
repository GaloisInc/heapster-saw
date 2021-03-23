{-# Language GADTs #-}
{-# Language RecordWildCards #-}
{-# Language LambdaCase #-}
{-# Language BlockArguments #-}
{-# Language RankNTypes #-}
{-# Language TemplateHaskell #-}
{-# Language TypeOperators #-}
{-# Language DataKinds #-}
{-# Language ImportQualifiedPost #-}
{-# Language ScopedTypeVariables #-}
{-# Language KindSignatures #-}
module Verifier.SAW.Heapster.TypeChecker where

import Data.Functor.Product
import Data.Functor.Constant
import GHC.TypeLits (Nat, KnownNat)
import GHC.Natural

import Data.Binding.Hobbits
import Data.Binding.Hobbits.MonadBind

import Prettyprinter hiding (comma, space)

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

lookupExprVar :: String -> TcEnv -> Maybe TypedName
lookupExprVar str = lookup str . tcEnvExprVars

mkTcEnv :: PermEnv -> TcEnv
mkTcEnv = TcEnv []

----------------------------------------------------------------------
-- * Type-checking type
----------------------------------------------------------------------

data TypeError = TypeError Pos String

newtype Tc a = Tc (TcEnv -> Either TypeError a)

instance Functor     Tc
instance Applicative Tc
instance Monad       Tc
instance MonadBind   Tc

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
        pure (Some (mkKnownReprObj (LLVMBlockRepr w)))
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
  do env <- tcAsk
     case lookupExprVar name env of
       Nothing -> tcError p "unknown variable"
       Just (Some tn) -> tcCastTyped p ty tn

tcExpr :: TypeRepr a -> AstExpr -> Tc (PermExpr a)
tcExpr ty (ExVar p name Nothing Nothing) = PExpr_Var <$> tcVar ty p name

tcExpr tp@LLVMShapeRepr{} (ExVar p name (Just args) Nothing) =
  do env <- tcAsk
     case lookupNamedShape (tcEnvPermEnv env) name of
       Just (SomeNamedShape _ arg_ctx mb_sh)
         | Just Refl <- testEquality (mbLift (fmap exprType mb_sh)) tp ->
           do sub <- tcStructFields p arg_ctx args
              pure (subst (substOfExprs sub) mb_sh)
       Just (SomeNamedShape _ _ mb_sh) ->
         tcError p $ renderDoc $ sep
         [ pretty "Named shape" <+> pretty name <+>
           pretty "is of incorrect type"
         , pretty "Expected:" <+> permPretty emptyPPInfo tp
         , pretty "Found:" <+>
           permPretty emptyPPInfo (mbLift (fmap exprType mb_sh)) ]
       Nothing -> tcError p ("Unknown shape name: " ++ name)

tcExpr _ (ExVar p _ Just{} _) = tcError p "Unexpected variable instantiation"
tcExpr _ (ExVar p _ _ Just{}) = tcError p "Unexpected variable offset"




tcExpr UnitRepr         e = tcUnit e
tcExpr NatRepr          e = tcNat e
tcExpr (BVRepr w)       e = withKnownNat w (tcBV e)
tcExpr (StructRepr fs)  e = tcStruct fs e
tcExpr LifetimeRepr     e = tcLifetime e
tcExpr (LLVMPointerRepr w) e = withKnownNat w (tcLLVMPointer w e)
tcExpr FunctionHandleRepr{} e = tcError (pos e) "expected functionhandle type" -- no literals
tcExpr PermListRepr     e = tcError (pos e) "expected permlist type" -- no literals
tcExpr RWModalityRepr   e = tcRWModality e
tcExpr (ValuePermRepr t) e = permToExpr <$> tcValPerm t e
tcExpr (LLVMShapeRepr w) e = withKnownNat w (tcLLVMShape e)

-- reprs that we explicitly do not support
tcExpr BoolRepr         e = tcError (pos e) "expected boolean"
tcExpr IntegerRepr      e = tcError (pos e) "expected integerl"
tcExpr AnyRepr          e = tcError (pos e) "expected any type"
tcExpr RealValRepr      e = tcError (pos e) "expected realval type"
tcExpr ComplexRealRepr  e = tcError (pos e) "expected realval type"
tcExpr IntrinsicRepr{}  e = tcError (pos e) "unknown intrinsic type"
tcExpr RecursiveRepr{}  e = tcError (pos e) "expected recursive type"
tcExpr FloatRepr{}      e = tcError (pos e) "expected float type"
tcExpr IEEEFloatRepr{}  e = tcError (pos e) "expected ieeefloat type"
tcExpr CharRepr         e = tcError (pos e) "expected char type"
tcExpr StringRepr{}     e = tcError (pos e) "expected string type"
tcExpr MaybeRepr{}      e = tcError (pos e) "expected maybe type"
tcExpr VectorRepr{}     e = tcError (pos e) "expected vector type"
tcExpr VariantRepr{}    e = tcError (pos e) "expected variant type"
tcExpr ReferenceRepr{}  e = tcError (pos e) "expected variant type"
tcExpr WordMapRepr{}    e = tcError (pos e) "expected wordmap type"
tcExpr StringMapRepr{}  e = tcError (pos e) "expected stringmap type"
tcExpr SymbolicArrayRepr{} e = tcError (pos e) "expected symbolicarray type"
tcExpr SymbolicStructRepr{} e = tcError (pos e) "expected symbolicstruct type"


tcUnit :: AstExpr -> Tc (PermExpr UnitType)
tcUnit ExUnit{} = pure PExpr_Unit
tcUnit e        = tcError (pos e) "expected unit type"

tcNat :: AstExpr -> Tc (PermExpr NatType)
tcNat (ExNat _ i) = pure (PExpr_Nat i)
tcNat e           = tcError (pos e) "expected unit type"

tcBV :: (KnownNat w, 1 <= w) => AstExpr -> Tc (PermExpr (BVType w))
tcBV (ExAdd _ x y) = bvAdd <$> tcBV x <*> tcBV y
tcBV e             = tcBVFactor e

-- Note: this could be more permissive
tcBVFactor :: (KnownNat w, 1 <= w) => AstExpr -> Tc (PermExpr (BVType w))
tcBVFactor (ExNat _ i) = pure (bvInt (fromIntegral i))
tcBVFactor (ExMul _ (ExNat _ i) (ExVar p name Nothing Nothing)) =
  do env <- tcAsk
     case lookupExprVar name env of
       Nothing -> tcError p "unknown variable"
       Just (Some tn) -> bvMult i . PExpr_Var <$> tcCastTyped p knownRepr tn
tcBVFactor (ExMul _ (ExVar p name Nothing Nothing) (ExNat _ i)) =
  do env <- tcAsk
     case lookupExprVar name env of
       Nothing -> tcError p "unknown variable"
       Just (Some tn) -> bvMult i . PExpr_Var <$> tcCastTyped p knownRepr tn
tcBVFactor (ExVar p name Nothing Nothing) =
  do env <- tcAsk
     case lookupExprVar name env of
       Nothing -> tcError p "unknown variable"
       Just (Some tn) -> PExpr_Var <$> tcCastTyped p knownRepr tn
tcBVFactor e = tcError (pos e) "expected bv factor"

tcStruct :: CtxRepr fs -> AstExpr -> Tc (PermExpr (StructType fs))
tcStruct ts (ExStruct p es) = PExpr_Struct <$> tcStructFields p (mkCruCtx ts) (reverse es)
tcStruct _ e = tcError (pos e) "expected struct type"

tcStructFields :: Pos -> CruCtx fs -> [AstExpr] -> Tc (PermExprs fs)
tcStructFields _ CruCtxNil [] = pure PExprs_Nil
tcStructFields p (CruCtxCons xs x) (y:ys) =
  do zs <- tcStructFields p xs ys
     z  <- tcExpr x y
     pure (zs :>: z)
tcStructFields p _ _ = tcError p "bad arity"

tcValuePerms :: Pos -> RAssign TypeRepr tys -> [AstExpr] -> Tc (RAssign ValuePerm tys)
tcValuePerms p tys es = tcValuePerms' p tys (reverse es)

tcValuePerms' :: Pos -> RAssign TypeRepr tps -> [AstExpr] -> Tc (RAssign ValuePerm tps)
tcValuePerms' _ MNil [] = pure MNil
tcValuePerms' p (xs :>: x) (y:ys) =
  do zs <- tcValuePerms' p xs ys
     z  <- tcValPerm x y
     pure (zs :>: z)
tcValuePerms' p _ _ = tcError p "bad arity"

tcRWModality :: AstExpr -> Tc (PermExpr RWModalityType)
tcRWModality ExRead {} = pure PExpr_Read
tcRWModality ExWrite{} = pure PExpr_Write
tcRWModality e         = tcError (pos e) "expected rwmodality"

tcLifetime :: AstExpr -> Tc (PermExpr LifetimeType)
tcLifetime ExAlways{} = pure PExpr_Always
tcLifetime e          = tcError (pos e) "expected lifetime"

tcLLVMShape :: (KnownNat w, 1 <= w) => AstExpr -> Tc (PermExpr (LLVMShapeType w))
tcLLVMShape ExEmptySh{} = pure PExpr_EmptyShape
tcLLVMShape (ExEqSh _ v) = PExpr_EqShape <$> tcExpr knownRepr v
tcLLVMShape (ExPtrSh _ maybe_l maybe_rw sh) =
  PExpr_PtrShape
  <$> traverse (tcExpr knownRepr) maybe_l
  <*> traverse (tcExpr knownRepr) maybe_rw
  <*> tcExpr knownRepr sh
tcLLVMShape (ExFieldSh _ w fld) = PExpr_FieldShape <$> tcLLVMFieldShape_ w fld
tcLLVMShape (ExArraySh _ len stride flds) =
  PExpr_ArrayShape
  <$> tcExpr knownRepr len
  <*> (Bytes . fromIntegral <$> tcNatural stride)
  <*> traverse (uncurry tcLLVMFieldShape_) flds
tcLLVMShape e = tcError (pos e) "expected llvmshape"

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
tcLLVMPointer _ (ExLlvmWord _ e) = PExpr_LLVMWord <$> tcBV e
tcLLVMPointer w (ExAdd _ (ExVar p name Nothing Nothing) off) = PExpr_LLVMOffset <$> tcVar (LLVMPointerRepr w) p name <*> tcBV off
tcLLVMPointer _ e = tcError (pos e) "expected llvmpointer"

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
           do args <- tcStructFields p (namedPermNameArgs rpn) argEs
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
             do args <- tcStructFields p (namedPermNameArgs npn) argEs
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
tcAtomicPerm _ e = tcError (pos e) "expected atomic perm"

tcPointerAtomic :: (KnownNat w, 1 <= w) => AstExpr -> Tc (AtomicPerm (LLVMPointerType w))
tcPointerAtomic (ExPtr p l rw off sz c) =
  llvmArrayFieldToAtomicPerm <$> tcArrayPerm (ArrayPerm p l rw off sz c)
tcPointerAtomic (ExArray _ x y z w) = Perm_LLVMArray <$> tcArrayAtomic x y z w
tcPointerAtomic (ExMemblock _ l rw off len sh) = Perm_LLVMBlock <$> tcMemblock l rw off len sh
tcPointerAtomic (ExFree      _ x  ) = Perm_LLVMFree <$> tcBV x
tcPointerAtomic (ExEqual     _ x y) = Perm_BVProp <$> (BVProp_Eq   <$> tcBV x <*> tcBV y)
tcPointerAtomic (ExNotEqual  _ x y) = Perm_BVProp <$> (BVProp_Neq  <$> tcBV x <*> tcBV y)
tcPointerAtomic (ExLessThan  _ x y) = Perm_BVProp <$> (BVProp_ULt  <$> tcBV x <*> tcBV y)
tcPointerAtomic (ExLessEqual _ x y) = Perm_BVProp <$> (BVProp_ULeq <$> tcBV x <*> tcBV y)
tcPointerAtomic e = tcError (pos e) "expected atomic pointer perm"

tcMemblock ::
  (KnownNat w, 1 <= w) =>
  Maybe AstExpr ->
  AstExpr -> AstExpr -> AstExpr -> AstExpr -> Tc (LLVMBlockPerm w)
tcMemblock l rw off len sh =
  do llvmBlockLifetime <- maybe (pure PExpr_Always) tcLifetime l
     llvmBlockRW       <- tcRWModality rw
     llvmBlockOffset   <- tcBV off
     llvmBlockLen      <- tcBV len
     llvmBlockShape    <- tcLLVMShape sh
     pure LLVMBlockPerm{..}

tcArrayAtomic ::
  (KnownNat w, 1 <= w) => AstExpr -> AstExpr -> AstExpr -> [ArrayPerm] -> Tc (LLVMArrayPerm w)
tcArrayAtomic off len stride fields =
  LLVMArrayPerm
  <$> tcBV off
  <*> tcBV len
  <*> (Bytes . fromIntegral <$> tcNatural stride)
  <*> traverse tcArrayPerm fields
  <*> pure []

tcArrayPerm :: forall w. (KnownNat w, 1 <= w) => ArrayPerm -> Tc (LLVMArrayField w)
tcArrayPerm (ArrayPerm _ l rw off sz c) =
  do llvmFieldLifetime <- maybe (pure PExpr_Always) tcLifetime l
     llvmFieldRW <- tcRWModality rw
     llvmFieldOffset <- tcBV off :: Tc (PermExpr (BVType w))
     Some (Pair w LeqProof) <- maybe (pure (Some (Pair (knownNat :: NatRepr w) LeqProof)))
                               tcPositive sz
     withKnownNat w do
      llvmFieldContents <- withKnownNat w (tcValPerm (LLVMPointerRepr w) c)
      pure (LLVMArrayField LLVMFieldPerm{..})

tcFrameAtomic :: (KnownNat w, 1 <= w) => AstExpr -> Tc (AtomicPerm (LLVMFrameType w))
tcFrameAtomic (ExLlvmFrame _ xs) =
  Perm_LLVMFrame <$> traverse (\(e,i) -> (,) <$> tcExpr knownRepr e <*> pure (fromIntegral i)) xs
tcFrameAtomic e = tcError (pos e) "expected atomic llvmframe"

tcStructAtomic :: CtxRepr tys -> AstExpr -> Tc (AtomicPerm (StructType tys))
tcStructAtomic tys (ExStruct p es) = Perm_Struct <$> tcValuePerms p (assignToRList tys) es
tcStructAtomic _ e = tcError (pos e) "expected atomic struct perm"

tcBlockAtomic :: (KnownNat w, 1 <= w) => AstExpr -> Tc (AtomicPerm (LLVMBlockType w))
tcBlockAtomic (ExShape _ e) = Perm_LLVMBlockShape <$> tcExpr knownRepr e
tcBlockAtomic e = tcError (pos e) "expected llvmblock atomicperm"

tcLifetimeAtomic :: AstExpr -> Tc (AtomicPerm LifetimeType)
tcLifetimeAtomic (ExLOwned _ x y) =
  do Some x' <- tcLOwnedPerms x
     Some y' <- tcLOwnedPerms y
     pure (Perm_LOwned x' y')
tcLifetimeAtomic (ExLCurrent _ l) =
  Perm_LCurrent <$> maybe (pure PExpr_Always) tcLifetime l
tcLifetimeAtomic e = tcError (pos e) "expected liftime atomic perm"

tcLOwnedPerms :: [(String,AstExpr)] -> Tc (Some LOwnedPerms)
tcLOwnedPerms [] = pure (Some MNil)
tcLOwnedPerms ((n,e):xs) =
  do env <- tcAsk
     Some (Typed tp x) <- case lookupExprVar n env of
                            Nothing -> tcError (pos e) "unknown variable"
                            Just x -> pure x
     p <- tcValPerm tp e
     lop <- case varAndPermLOwnedPerm (VarAndPerm x p) of
              Just lop -> return lop
              Nothing -> tcError (pos e) ("Not a valid lifetime ownership permission: "
                                         ++ permPrettyString emptyPPInfo p)
     Some lops <- tcLOwnedPerms xs
     pure (Some (lops :>: lop))

tcPermOffset :: TypeRepr a -> Pos -> Maybe AstExpr -> Tc (PermOffset a)
tcPermOffset _ _ Nothing = pure NoPermOffset
tcPermOffset (LLVMPointerRepr w) _ (Just i) = withKnownNat w (LLVMPermOffset <$> tcBV i)
tcPermOffset _ p _ = tcError p "Unexpected variable offset"

tcNatural :: AstExpr -> Tc Natural
tcNatural (ExNat _ i) = pure i
tcNatural e = tcError (pos e) "integer literal required"

tcPositive :: AstExpr -> Tc (Some (Product NatRepr (LeqProof 1)))
tcPositive e =
  do i <- tcNatural e
     withPositive (pos e) "positive required" i \w -> pure (Some (Pair w LeqProof))

tcCtx :: [(String, AstType)] -> Tc (Some ParsedCtx)
tcCtx []         = pure (Some emptyParsedCtx)
tcCtx ((n,t):xs) = preconsSomeParsedCtx n <$> tcType t <*> tcCtx xs
