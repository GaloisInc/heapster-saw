{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Verifier.SAW.Heapster.RustTypes where

import Prelude hiding (span)

import Data.Maybe
import Data.List hiding (span)
import GHC.TypeLits
import Data.Functor.Constant
import Data.Functor.Product
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Trans.Maybe

import Data.Parameterized.BoolRepr
import Data.Parameterized.Some

import Data.Binding.Hobbits
import Data.Binding.Hobbits.MonadBind
import qualified Data.Type.RList as RL
import qualified Data.Binding.Hobbits.NameSet as NameSet

import Language.Rust.Syntax
import Language.Rust.Parser
import Language.Rust.Data.Ident (Ident(..))

import Prettyprinter as PP

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel hiding (Mutability(..))

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions


----------------------------------------------------------------------
-- * Helper Definitions for Translation
----------------------------------------------------------------------

-- | A permission of some llvm pointer type
data SomeLLVMPerm =
  forall w. (1 <= w, KnownNat w) => SomeLLVMPerm (ValuePerm (LLVMPointerType w))

$(mkNuMatching [t| SomeLLVMPerm |])

-- | Info used for converting Rust types to shapes
data RustConvInfo =
  RustConvInfo { rciPermEnv :: PermEnv,
                 rciCtx :: [(String, TypedName)] }

-- | The default, top-level 'RustConvInfo' for a given 'PermEnv'
mkRustConvInfo :: PermEnv -> RustConvInfo
mkRustConvInfo env =
  RustConvInfo { rciPermEnv = env, rciCtx = [] }

-- | The Rust conversion monad is just a state-error monad
newtype RustConvM a =
  RustConvM { unRustConvM :: ReaderT RustConvInfo (Except String) a }
  deriving (Functor, Applicative, Monad,
            MonadError String, MonadReader RustConvInfo)

instance MonadFail RustConvM where
  fail = RustConvM . throwError

instance MonadBind RustConvM where
  mbM mb_m = RustConvM $ mbM $ fmap unRustConvM mb_m

-- | Prefix any error message with location information
atSpan :: Span -> RustConvM a -> RustConvM a
atSpan span m =
  catchError m (\msg -> fail ("At " ++ show span ++ ": " ++ msg))

-- | Run a Rust conversion computation with the given 'RustConvInfo', lifting
-- any errors into the outer monad
runLiftRustConvM :: MonadFail m => RustConvInfo -> RustConvM a -> m a
runLiftRustConvM info (RustConvM m) =
  case runExcept (runReaderT m info) of
    Left err -> fail err
    Right x -> return x

-- | Look up the 'TypedName' associated with a 'String' name
lookupTypedName :: String -> RustConvM TypedName
lookupTypedName str =
  fmap (lookup str) (rciCtx <$> ask) >>= \case
  Just n -> return n
  Nothing -> fail ("Could not find variable: " ++ show str)

-- | Look up a 'Name' with a given type
lookupName :: String -> TypeRepr a -> RustConvM (Name a)
lookupName str tp =
  lookupTypedName str >>= \n -> castTypedM "variable" tp n

-- | The conversion of a context of Rust type and lifetime variables
type RustCtx = RAssign (Product (Constant String) TypeRepr)

-- | Build a 'RustCtx' for a single variable
rustCtx1 :: String -> TypeRepr a -> RustCtx (RNil :> a)
rustCtx1 name tp = MNil :>: Pair (Constant name) tp

-- | Extract a 'CruCtx' from a 'RustCtx'
rustCtxCtx :: RustCtx ctx -> CruCtx ctx
rustCtxCtx = cruCtxOfTypes . RL.map (\(Pair _ tp) -> tp)

-- | Build a 'RustCtx' from the given variable names, all having the same type
rustCtxOfNames :: TypeRepr a -> [String] -> Some RustCtx
rustCtxOfNames tp =
  foldl (\(Some ctx) name -> Some (ctx :>: Pair (Constant name) tp)) (Some MNil)

-- | Run a 'RustConvM' computation in a context of bound type-level variables
inRustCtx :: NuMatching a => RustCtx ctx -> RustConvM a ->
             RustConvM (Mb ctx a)
inRustCtx ctx m =
  mbM $ nuMulti ctx $ \ns ->
  let ns_ctx =
        RL.toList $ RL.map2 (\n (Pair (Constant str) tp) ->
                              Constant (str, Some (Typed tp n))) ns ctx in
  local (\info -> info { rciCtx = ns_ctx ++ rciCtx info }) m

-- | Class for a generic "conversion from Rust" function, given the bit width of
-- the pointer type
class RsConvert w a b | w a -> b where
  rsConvert :: (1 <= w, KnownNat w) => prx w -> a -> RustConvM b


----------------------------------------------------------------------
-- * Converting Named Rust Types
----------------------------------------------------------------------

-- FIXME HERE: I think we no longer need SomeShapeFun

-- | A shape function with existentially quantified arguments
data SomeShapeFun w =
  forall args. SomeShapeFun (CruCtx args) (Mb args (PermExpr (LLVMShapeType w)))

-- | A sequence of 'PermExprs' along with their types
type TypedPermExprs = RAssign (Typed PermExpr)

-- | The empty sequence of typed permission expressions
emptyTypedPermExprs :: Some TypedPermExprs
emptyTypedPermExprs = Some MNil

appendTypedExprs :: Some TypedPermExprs -> Some TypedPermExprs ->
                    Some TypedPermExprs
appendTypedExprs (Some exprs1) (Some exprs2) = Some (RL.append exprs1 exprs2)

-- | Extract a type context from a 'TypedPermExprs'
typedPermExprsCtx :: TypedPermExprs ctx -> CruCtx ctx
typedPermExprsCtx = cruCtxOfTypes . RL.map typedType

-- | Extract the expressions from a 'TypedPermExprs'
typedPermExprsExprs :: TypedPermExprs ctx -> PermExprs ctx
typedPermExprsExprs = rassignToExprs . RL.map typedObj

-- | Convert a list of epxressions of a given type to a TypedPermExprs
typedExprsOfList :: TypeRepr a -> [PermExpr a] -> Some TypedPermExprs
typedExprsOfList tp =
  foldl (\(Some es) e -> Some (es :>: Typed tp e)) (Some MNil)

-- | Apply a 'SomeShapeFun', if possible
tryApplySomeShapeFun :: SomeShapeFun w -> Some TypedPermExprs ->
                        Maybe (PermExpr (LLVMShapeType w))
tryApplySomeShapeFun (SomeShapeFun ctx mb_sh) (Some exprs)
  | Just Refl <- testEquality ctx (typedPermExprsCtx exprs) =
    Just $ subst (substOfExprs $ typedPermExprsExprs exprs) mb_sh
tryApplySomeShapeFun _ _ = Nothing

-- | Build a 'SomeShapeFun' with no arguments
constShapeFun :: PermExpr (LLVMShapeType w) -> SomeShapeFun w
constShapeFun sh = SomeShapeFun CruCtxNil (emptyMb sh)

-- | Build the shape @fieldsh(exists z:bv sz.eq(llvmword(z))@
sizedIntShapeFun :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                    prx1 w -> prx2 sz -> SomeShapeFun w
sizedIntShapeFun _ sz =
  constShapeFun $ PExpr_FieldShape (LLVMFieldShape $
                                    ValPerm_Exists $ llvmExEqWord sz)

-- | A table for converting Rust base types to shapes
namedTypeTable :: (1 <= w, KnownNat w) => prx w -> [(String,SomeShapeFun w)]
namedTypeTable w =
  [("bool", sizedIntShapeFun @_ @1 w Proxy),
   ("i8", sizedIntShapeFun @_ @8 w Proxy),
   ("u8", sizedIntShapeFun @_ @8 w Proxy),
   ("i16", sizedIntShapeFun @_ @16 w Proxy),
   ("u16", sizedIntShapeFun @_ @16 w Proxy),
   ("i32", sizedIntShapeFun @_ @32 w Proxy),
   ("u32", sizedIntShapeFun @_ @32 w Proxy),
   ("i64", sizedIntShapeFun @_ @64 w Proxy),
   ("u64", sizedIntShapeFun @_ @64 w Proxy),

   -- isize and usize are the same size as pointers, which is w
   ("isize", sizedIntShapeFun w w),
   ("usize", sizedIntShapeFun w w),

   -- Strings contain three fields: a pointer, a length, and a capacity
   ("String",
    constShapeFun (PExpr_ExShape $ nu $ \cap ->
                    (PExpr_SeqShape
                     -- The pointer to an array of bytes
                     (PExpr_PtrShape Nothing Nothing $
                      PExpr_ArrayShape (PExpr_Var cap) 1
                      [LLVMFieldShape $ ValPerm_Exists $ llvmExEqWord $ Proxy @8])
                     (PExpr_SeqShape
                      -- The length value
                      (PExpr_FieldShape $ LLVMFieldShape $
                       ValPerm_Exists $ llvmExEqWord w)
                      -- The capacity
                      (PExpr_FieldShape $ LLVMFieldShape $ ValPerm_Eq $
                       PExpr_LLVMWord $ PExpr_Var cap)))))
   ]

-- | A fully qualified Rust path without any of the parameters; e.g.,
-- @Foo<X>::Bar<Y,Z>::Baz@ just becomes @[Foo,Bar,Baz]@
newtype RustName = RustName [Ident]

instance Show RustName where
  show (RustName ids) = concat $ intersperse "::" $ map show ids

instance RsConvert w RustName SomeNamedShape where
  rsConvert w (RustName elems) =
    -- FIXME: figure out how to actually resolve names; for now we just look at
    -- the last string component...
    do let str = name $ last elems
       env <- rciPermEnv <$> ask
       let maybe_nmsh = lookupNamedShape env str
       case maybe_nmsh of
         Just nmsh -> return nmsh
         Nothing -> fail ("Unkown Rust type name: " ++ str)

-- | Get the "name" = sequence of identifiers out of a Rust path
rsPathName :: Path a -> RustName
rsPathName (Path _ segments _) =
  RustName $ map (\(PathSegment rust_id _ _) -> rust_id) segments

-- | Get all the parameters out of a Rust path
rsPathParams :: Path a -> [PathParameters a]
rsPathParams (Path _ segments _) =
  mapMaybe (\(PathSegment _ maybe_params _) -> maybe_params) segments


----------------------------------------------------------------------
-- * Converting Rust Types to Heapster Shapes
----------------------------------------------------------------------

instance RsConvert w Mutability (PermExpr RWModalityType) where
  rsConvert _ Mutable = return PExpr_Write
  rsConvert _ Immutable = return PExpr_Read

instance RsConvert w (Lifetime Span) (PermExpr LifetimeType) where
  rsConvert _ (Lifetime "static" _) = return PExpr_Always
  rsConvert _ (Lifetime l span) =
    PExpr_Var <$> atSpan span (lookupName l knownRepr)

instance RsConvert w (PathParameters Span) (Some TypedPermExprs) where
  rsConvert w (AngleBracketed rust_ls rust_tps [] _) =
    do ls <- mapM (rsConvert w) rust_ls
       shs <- mapM (rsConvert w) rust_tps
       return $ appendTypedExprs
         (typedExprsOfList knownRepr ls) (typedExprsOfList knownRepr shs)

instance RsConvert w [PathParameters Span] (Some TypedPermExprs) where
  rsConvert w paramss =
    foldr appendTypedExprs emptyTypedPermExprs <$> mapM (rsConvert w) paramss

instance RsConvert w (Ty Span) (PermExpr (LLVMShapeType w)) where
  rsConvert _ (Rptr _ _ (Slice _ _) _) =
    error "FIXME: pointers to slice types are not currently supported"
  rsConvert w (Rptr (Just rust_l) Mutable tp' _) =
    do l <- rsConvert w rust_l
       sh <- rsConvert w tp'
       return $ PExpr_PtrShape Nothing (Just l) sh
  rsConvert w (Rptr (Just rust_l) Immutable tp' _) =
    do l <- rsConvert w rust_l
       sh <- rsConvert w tp'
       return $ PExpr_PtrShape (Just PExpr_Read) (Just l) sh
  rsConvert w (PathTy Nothing path _) =
    do SomeNamedShape nmsh <- rsConvert w (rsPathName path)
       Some typed_args <- rsConvert w (rsPathParams path)
       case (testEquality (typedPermExprsCtx typed_args) (namedShapeArgs nmsh),
             testEquality (natRepr w) (natRepr nmsh)) of
         (Just Refl, Just Refl) ->
           return (PExpr_NamedShape Nothing Nothing nmsh $
                   typedPermExprsExprs typed_args)
         (Nothing, _) ->
           fail $ renderDoc $ fillSep
           [pretty "Arguments for" <+> pretty (namedShapeName nmsh)
            <+> pretty "of incorrect type",
            pretty "Expected:" <+> permPretty emptyPPInfo (namedShapeArgs nmsh),
            pretty "Actual:"
            <+> permPretty emptyPPInfo (typedPermExprsCtx typed_args)]
         (_, Nothing) ->
           fail $ renderDoc $ fillSep
           [pretty "Incorrect size of shape" <+> pretty (namedShapeName nmsh),
            pretty "Expected:" <+> pretty (intValue (natRepr w)),
            pretty "Actual:" <+> pretty (intValue (natRepr nmsh))]
  rsConvert (w :: prx w) (BareFn _ abi rust_ls2 fn_tp span) =
    do Some3FunPerm fun_perm <- rsConvertMonoFun w span abi rust_ls2 fn_tp
       let args = funPermArgs fun_perm
       case cruCtxToReprEq args of
         Refl ->
           return $ PExpr_FieldShape $ LLVMFieldShape @w @w $ ValPerm_Conj1 $
           Perm_LLVMFunPtr
           (FunctionHandleRepr (cruCtxToRepr args) (funPermRet fun_perm)) $
           ValPerm_Conj1 $ Perm_Fun fun_perm
  rsConvert _ tp = fail ("Rust type not supported: " ++ show tp)

instance RsConvert w (Arg Span) (PermExpr (LLVMShapeType w)) where
  rsConvert w (Arg _ tp _) = rsConvert w tp
  rsConvert _ _ = error "rsConvert (Arg): argument form not yet handled"


----------------------------------------------------------------------
-- * Computing the ABI-Specific Layout of Rust Types
----------------------------------------------------------------------

-- | An argument layout is a sequence of Crucible types for 0 or more function
-- arguments along with permissions on them, which could be existential in some
-- number of ghost arguments. The ghost arguments cannot have permissions on
-- them, so that we can create struct permissions from just the arg perms.
data ArgLayout where
  ArgLayout :: KnownCruCtx ghosts -> KnownCruCtx args ->
               Mb ghosts (ValuePerms args) -> ArgLayout

instance Semigroup ArgLayout where
  ArgLayout ghosts1 args1 mb_ps1 <> ArgLayout ghosts2 args2 mb_ps2 =
    ArgLayout (RL.append ghosts1 ghosts2) (RL.append args1 args2) $
    mbCombine $ fmap (\ps1 -> fmap (\ps2 -> RL.append ps1 ps2) mb_ps2) mb_ps1

instance Monoid ArgLayout where
  mempty = ArgLayout MNil MNil (emptyMb $ MNil)

-- | Construct an 'ArgLayout' for a single argument with no ghost variables
argLayout1 :: KnownRepr TypeRepr a => ValuePerm a -> ArgLayout
argLayout1 p =
  ArgLayout MNil (MNil :>: KnownReprObj) $ emptyMb (MNil :>: p)

-- | Convert an 'ArgLayout' in a name-binding into an 'ArgLayout' with an
-- additional ghost argument for the bound name
mbArgLayout :: KnownRepr TypeRepr a => Binding a ArgLayout -> ArgLayout
mbArgLayout [nuP| ArgLayout ghosts args mb_ps |] =
  ArgLayout (mbLift ghosts :>: KnownReprObj) (mbLift args) (mbCombine $
                                                            mbSwap mb_ps)

-- | Convert an 'ArgLayout' to a permission on a @struct@ of its arguments
argLayoutStructPerm :: ArgLayout -> Some (Typed ValuePerm)
argLayoutStructPerm (ArgLayout ghosts (MNil :>: KnownReprObj) mb_perms) =
  Some $ Typed knownRepr $
  valPermExistsMulti ghosts $ fmap (\(_ :>: perm) -> perm) mb_perms
argLayoutStructPerm (ArgLayout ghosts args mb_perms)
  | args_repr <- cruCtxToRepr (knownCtxToCruCtx args)
  , Refl <- cruCtxToReprEq (knownCtxToCruCtx args) =
    Some $ Typed (StructRepr args_repr) $
    valPermExistsMulti ghosts $ fmap (ValPerm_Conj1 . Perm_Struct) mb_perms

-- | Convert a shape to a writeable block permission with that shape, or fail if
-- the length of the shape is not defined
--
-- FIXME: maybe this goes in the 'Permissions' module?
shapeToBlock :: (1 <= w, KnownNat w) => PermExpr (LLVMShapeType w) ->
                Maybe (LLVMBlockPerm w)
shapeToBlock sh
  | Just len <- llvmShapeLength sh =
    Just $ LLVMBlockPerm
    { llvmBlockRW = PExpr_Write, llvmBlockLifetime = PExpr_Always,
      llvmBlockOffset = bvInt 0, llvmBlockLen = len, llvmBlockShape = sh }
shapeToBlock _ = Nothing

-- | Convert a shape to a writeable @memblock@ permission with that shape, or
-- fail if the length of the shape is not defined
--
-- FIXME: maybe this goes in the 'Permissions' module?
shapeToBlockPerm :: (1 <= w, KnownNat w) => PermExpr (LLVMShapeType w) ->
                    Maybe (ValuePerm (LLVMPointerType w))
shapeToBlockPerm = fmap ValPerm_LLVMBlock . shapeToBlock

-- | Function permission that is existential over all types
data Some3FunPerm =
  forall ghosts args ret. Some3FunPerm (FunPerm ghosts args ret)

instance PermPretty Some3FunPerm where
  permPrettyM (Some3FunPerm fun_perm) = permPrettyM fun_perm

-- | Try to convert a 'Some3FunPerm' to a 'SomeFunPerm' at a specific type
un3SomeFunPerm :: CruCtx args -> TypeRepr ret -> Some3FunPerm ->
                  RustConvM (SomeFunPerm args ret)
un3SomeFunPerm args ret (Some3FunPerm fun_perm)
  | Just Refl <- testEquality args (funPermArgs fun_perm)
  , Just Refl <- testEquality ret (funPermRet fun_perm) =
    return $ SomeFunPerm fun_perm
un3SomeFunPerm args ret (Some3FunPerm fun_perm) =
  fail $ renderDoc $ fillSep
  [pretty "Incorrect LLVM type for function permission:",
   permPretty emptyPPInfo fun_perm,
   pretty "Expected type:"
   <+> permPretty emptyPPInfo args <+> pretty "=>"
   <+> permPretty emptyPPInfo ret,
   pretty "Actual type:"
   <+> permPretty emptyPPInfo (funPermArgs fun_perm)
   <+> pretty "=>" <+> permPretty emptyPPInfo (funPermRet fun_perm)
   ]

-- | Build a function permission from an 'ArgLayout' plus return permission
funPerm3FromArgLayout :: ArgLayout -> TypeRepr ret -> ValuePerm ret ->
                         Some3FunPerm
funPerm3FromArgLayout (ArgLayout ghosts args mb_arg_perms) ret_tp ret_perm =
  let gs_args_prxs = RL.map (const Proxy) (RL.append ghosts args) in
  Some3FunPerm $ FunPerm (knownCtxToCruCtx ghosts) (knownCtxToCruCtx args)
  ret_tp
  (extMbMulti args $
   fmap (RL.append $ RL.map (const ValPerm_True) ghosts) mb_arg_perms)
  (nuMulti (gs_args_prxs :>: Proxy) $ const
   (RL.map (const ValPerm_True) gs_args_prxs :>: ret_perm))

-- | Extend a name binding by adding a name in the middle
extMbMiddle :: prx1 ctx1 -> RAssign prx2 ctx2 -> prxb b ->
               Mb (ctx1 :++: ctx2) a ->
               Mb (ctx1 :++: ((RNil :> b) :++: ctx2)) a
extMbMiddle (_ :: prx1 ctx1) ctx2 (_ :: prxb b) mb_a =
  mbCombine $ fmap (mbCombine . nu @_ @b . const) $
  mbSeparate @_ @ctx1 ctx2 mb_a

-- | Insert an object into the middle of an 'RAssign'
rassignInsertMiddle :: prx1 ctx1 -> RAssign prx2 ctx2 -> f b ->
                       RAssign f (ctx1 :++: ctx2) ->
                       RAssign f (ctx1 :++: ((RNil :> b) :++: ctx2))
rassignInsertMiddle ctx1 ctx2 fb fs =
  let (fs1, fs2) = RL.split ctx1 ctx2 fs in
  RL.append fs1 (RL.append (MNil :>: fb) fs2)

-- | Prepend an argument with input and output perms to a 'Some3FunPerm'
funPerm3PrependArg :: TypeRepr arg -> ValuePerm arg -> ValuePerm arg ->
                      Some3FunPerm -> Some3FunPerm
funPerm3PrependArg arg_tp arg_in arg_out (Some3FunPerm
                                          (FunPerm ghosts args ret
                                           ps_in ps_out)) =
  let args_prxs = cruCtxProxies args in
  Some3FunPerm $ FunPerm ghosts (appendCruCtx (singletonCruCtx arg_tp) args) ret
  (extMbMiddle ghosts args_prxs arg_tp $
   fmap (rassignInsertMiddle ghosts args_prxs arg_in) ps_in)
  (extMbMiddle ghosts (args_prxs :>: Proxy) arg_tp $
   fmap (rassignInsertMiddle ghosts (args_prxs :>: Proxy) arg_out) ps_out)

mbSeparatePrx :: prx1 ctx1 -> RAssign prx2 ctx2 -> Mb (ctx1 :++: ctx2) a ->
                 Mb ctx1 (Mb ctx2 a)
mbSeparatePrx _ = mbSeparate

mbAssoc :: prx1 ctx1 -> RAssign prx2 ctx2 -> RAssign prx3 ctx3 ->
           Mb (ctx1 :++: (ctx2 :++: ctx3)) a ->
           Mb ((ctx1 :++: ctx2) :++: ctx3) a
mbAssoc ctx1 ctx2 ctx3 mb_a =
  mbCombine $ mbCombine $ fmap (mbSeparatePrx ctx2 ctx3) $
  mbSeparatePrx ctx1 (RL.append (RL.map (const Proxy) ctx2)
                      (RL.map (const Proxy) ctx3)) mb_a

mbCombineAssoc :: prx1 ctx1 -> prx2 ctx2 -> RAssign prx3 ctx3 ->
                  Mb ctx1 (Mb (ctx2 :++: ctx3) a) ->
                  Mb ((ctx1 :++: ctx2) :++: ctx3) a
mbCombineAssoc _ ctx2 ctx3 =
  mbCombine . mbCombine . fmap (mbSeparatePrx ctx2 ctx3)

assocAppend :: RAssign f ctx1 -> prx2 ctx2 -> RAssign prx3 ctx3 ->
               RAssign f (ctx2 :++: ctx3) ->
               RAssign f ((ctx1 :++: ctx2) :++: ctx3)
assocAppend fs1 ctx2 ctx3 fs23 =
  let (fs2, fs3) = RL.split ctx2 ctx3 fs23 in
  RL.append (RL.append fs1 fs2) fs3

-- | Add ghost variables for the bound names in a 'Some3FunPerm' in a binding
mbGhostsFunPerm3 :: CruCtx new_ghosts -> Mb new_ghosts Some3FunPerm ->
                    Some3FunPerm
mbGhostsFunPerm3 new_ghosts [nuP| Some3FunPerm
                                (FunPerm ghosts args ret ps_in ps_out) |] =
  let new_prxs = cruCtxProxies new_ghosts
      ghosts_prxs = cruCtxProxies $ mbLift ghosts
      args_prxs = cruCtxProxies $ mbLift args in
  Some3FunPerm $ FunPerm (appendCruCtx new_ghosts $
                          mbLift ghosts) (mbLift args) (mbLift ret)
  (mbAssoc new_prxs ghosts_prxs args_prxs $
   fmap (assocAppend (RL.map (const ValPerm_True) new_prxs)
         ghosts_prxs args_prxs) $ mbCombine ps_in)
  (mbAssoc new_prxs ghosts_prxs (args_prxs :>: Proxy) $
   fmap (assocAppend (RL.map (const ValPerm_True) new_prxs)
         ghosts_prxs (args_prxs :>: Proxy)) $ mbCombine ps_out)

-- | Try to compute the layout of a structure of the given shape as a value,
-- over 1 or more registers, if this is possible
layoutArgShapeByVal :: (1 <= w, KnownNat w) => Abi ->
                       PermExpr (LLVMShapeType w) ->
                       MaybeT RustConvM ArgLayout

-- The empty shape --> no values
layoutArgShapeByVal Rust PExpr_EmptyShape = return mempty

-- Named shapes that unfold --> layout their unfoldings
layoutArgShapeByVal Rust (PExpr_NamedShape rw l nmsh args)
  | TrueRepr <- namedShapeCanUnfoldRepr nmsh
  , Just sh' <- unfoldModalizeNamedShape rw l nmsh args =
    layoutArgShapeByVal Rust sh'

-- Opaque named shapes that are bigger than 16 bytes --> not laid out by value
--
-- FIXME: if an opaque named shape somehow corresponds to > 2 fields, it is also
-- not laid out by value
layoutArgShapeByVal Rust sh@(PExpr_NamedShape _ _ nmsh _)
  | not (namedShapeCanUnfold nmsh)
  , Just len <- llvmShapeLength sh
  , bvLt (bvInt 16) len =
    mzero

-- Opaque named shapes that could potentially be laid out by value are an error,
-- because we do not know their representation
layoutArgShapeByVal Rust sh@(PExpr_NamedShape _ _ nmsh _)
  | not (namedShapeCanUnfold nmsh) =
    lift $ fail $ renderDoc
    (pretty "layoutArgShapeByVal: Cannot lay out opaque named shape by value:"
     <+> pretty (namedShapeName nmsh))

-- The ptr shape --> a single pointer value, if we know its length
layoutArgShapeByVal Rust (PExpr_PtrShape maybe_rw maybe_l sh)
  | Just bp <- llvmBlockAdjustModalities maybe_rw maybe_l <$> shapeToBlock sh =
    return $ argLayout1 $ ValPerm_LLVMBlock bp

-- If we don't know the length of our pointer, we can't lay it out at all
layoutArgShapeByVal Rust (PExpr_PtrShape _ _ sh) =
  lift $ fail $ renderDoc $ fillSep
  [pretty "layoutArgShapeByVal: Shape with unknown length:",
   permPretty emptyPPInfo sh]

-- A field shape --> the contents of the field
layoutArgShapeByVal Rust (PExpr_FieldShape (LLVMFieldShape p)) =
  return $ argLayout1 p

-- Array shapes have unknown length, and so are never passed by value
layoutArgShapeByVal Rust (PExpr_ArrayShape _ _ _) = mzero

-- Sequence shapes are only laid out as values in the Rust ABI if the result has
-- at most two fields
layoutArgShapeByVal Rust (PExpr_SeqShape sh1 sh2) =
  do layout1 <- layoutArgShapeByVal Rust sh1
     layout2 <- layoutArgShapeByVal Rust sh2
     case (mappend layout1 layout2) of
       layout@(ArgLayout _ args _)
         | length (RL.mapToList (const Proxy) args) <= 2 -> return layout
       _ -> mzero

-- Disjunctive shapes are only laid out as values in the Rust ABI if both sides
-- have the same number and sizes of arguments. Note that Heapster currently
-- cannot handle this optimization, and so this is an error, but if the shape
-- cannot be laid out as values then we return Nothing without an error.
layoutArgShapeByVal Rust sh@(PExpr_OrShape sh1 sh2) =
  do layout1 <- layoutArgShapeByVal Rust sh1
     layout2 <- layoutArgShapeByVal Rust sh2
     case (layout1, layout2) of
       (ArgLayout _ args1 _, ArgLayout _ args2 _)
         | Just Refl <-
           testEquality (knownCtxToCruCtx args1) (knownCtxToCruCtx args2) ->
           lift $ fail $ renderDoc $ fillSep
           [pretty "layoutArgShapeByVal: Optimizing disjunctive shapes not yet supported for shape:",
            permPretty emptyPPInfo sh]
       _ -> mzero

-- For existential shapes, just add the existential variable to the ghosts
layoutArgShapeByVal Rust (PExpr_ExShape mb_sh) =
  mbArgLayout <$> mbM (fmap (layoutArgShapeByVal Rust) mb_sh)

layoutArgShapeByVal Rust sh =
  lift $ fail $ renderDoc $ fillSep
  [pretty "layoutArgShapeByVal: Unsupported shape:", permPretty emptyPPInfo sh]
layoutArgShapeByVal abi _ =
  lift $ fail ("layoutArgShapeByVal: Unsupported ABI: " ++ show abi)


-- | Try to compute the layout of a structure of the given shape as a value,
-- over 1 or more registers, if this is possible. Otherwise convert the shape to
-- an LLVM block permission.
layoutArgShapeOrBlock :: (1 <= w, KnownNat w) => Abi ->
                         PermExpr (LLVMShapeType w) ->
                         RustConvM (Either (LLVMBlockPerm w) ArgLayout)
layoutArgShapeOrBlock abi sh =
  runMaybeT (layoutArgShapeByVal abi sh) >>= \case
  Just layout -> return $ Right layout
  Nothing | Just bp <- shapeToBlock sh -> return $ Left bp
  _ ->
    fail $ renderDoc $ fillSep
    [pretty "layoutArgShapeOrBlock: Could not layout shape with unknown size:",
     permPretty emptyPPInfo sh]

-- | Compute the layout of an argument with the given shape as 1 or more
-- register arguments of a function
layoutArgShape :: (1 <= w, KnownNat w) => Abi ->
                  PermExpr (LLVMShapeType w) -> RustConvM ArgLayout
layoutArgShape abi sh =
  layoutArgShapeOrBlock abi sh >>= \case
  Right layout -> return layout
  Left bp -> return $ argLayout1 $ ValPerm_LLVMBlock bp

-- | Compute the layout for the inputs and outputs of a function with the given
-- shapes as arguments and return value as a function permission
layoutFun :: (1 <= w, KnownNat w) => Abi ->
             [PermExpr (LLVMShapeType w)] -> PermExpr (LLVMShapeType w) ->
             RustConvM Some3FunPerm
layoutFun abi arg_shs ret_sh =
  do args_layout <- mconcat <$> mapM (layoutArgShape abi) arg_shs
     ret_layout_eith <- layoutArgShapeOrBlock abi ret_sh
     case ret_layout_eith of
       Right ret_layout
         | Some (Typed ret_tp ret_p) <- argLayoutStructPerm ret_layout ->
           return $ funPerm3FromArgLayout args_layout ret_tp ret_p
       Left bp ->
         return $
         funPerm3PrependArg knownRepr
         (ValPerm_LLVMBlock $ bp { llvmBlockShape = PExpr_EmptyShape})
         (ValPerm_LLVMBlock bp) $
         funPerm3FromArgLayout args_layout UnitRepr ValPerm_True


----------------------------------------------------------------------
-- * Converting Function Types
----------------------------------------------------------------------

-- | A name-binding over some list of types
data SomeTypedMb a where
  SomeTypedMb :: CruCtx ctx -> Mb ctx a -> SomeTypedMb a

instance Functor SomeTypedMb where
  fmap f (SomeTypedMb ctx mb_a) = SomeTypedMb ctx (fmap f mb_a)

instance Applicative SomeTypedMb where
  pure a = SomeTypedMb CruCtxNil $ emptyMb a
  liftA2 f (SomeTypedMb ctx1 mb_a1) (SomeTypedMb ctx2 mb_a2) =
    SomeTypedMb (appendCruCtx ctx1 ctx2) $ mbCombine $
    flip fmap mb_a1 $ \a1 -> flip fmap mb_a2 $ \a2 -> f a1 a2

-- | Abstract over all the read/write and lifetime modalities in an
-- 'LOwnedPerms' sequence
abstractMbLOPsModalities :: Mb ctx (LOwnedPerms tps) ->
                            SomeTypedMb (Mb ctx (LOwnedPerms tps))
abstractMbLOPsModalities lops@[nuP| MNil |] = pure lops
abstractMbLOPsModalities [nuP| lops :>: LOwnedPermField mb_e mb_fp |] =
  liftA2 (mbMap2 (:>:))
  (abstractMbLOPsModalities lops)
  (SomeTypedMb (CruCtxCons (CruCtxCons CruCtxNil RWModalityRepr) LifetimeRepr) $
   nuMulti (MNil :>: Proxy :>: Proxy) $ \(_ :>: rw :>: l) ->
    mbMap2 (\e fp ->
             LOwnedPermField e (fp { llvmFieldRW = PExpr_Var rw,
                                     llvmFieldLifetime = PExpr_Var l }))
    mb_e mb_fp)
abstractMbLOPsModalities [nuP| lops :>: LOwnedPermBlock mb_e mb_bp |] =
  liftA2 (mbMap2 (:>:))
  (abstractMbLOPsModalities lops)
  (SomeTypedMb (CruCtxCons (CruCtxCons CruCtxNil RWModalityRepr) LifetimeRepr) $
   nuMulti (MNil :>: Proxy :>: Proxy) $ \(_ :>: rw :>: l) ->
    mbMap2 (\e bp ->
             LOwnedPermBlock e (bp { llvmBlockRW = PExpr_Var rw,
                                     llvmBlockLifetime = PExpr_Var l }))
    mb_e mb_bp)
abstractMbLOPsModalities [nuP| lops :>: lop@(LOwnedPermLifetime _ _ _) |] =
  liftA2 (mbMap2 (:>:)) (abstractMbLOPsModalities lops) (pure lop)


-- | Find all field or block permissions containing lifetime @l@ and return them
-- as an 'LOwnedPerms' list
lownedPermsForLifetime :: ExprVar LifetimeType -> DistPerms ctx ->
                          RustConvM (Some LOwnedPerms)
lownedPermsForLifetime _ MNil = return (Some MNil)
lownedPermsForLifetime l (perms :>: VarAndPerm x (ValPerm_LLVMField fp))
  | NameSet.member l (freeVars fp) =
    do Some lops <- lownedPermsForLifetime l perms
       return $ Some $ (lops :>: LOwnedPermField (PExpr_Var x) fp)
lownedPermsForLifetime l (perms :>: VarAndPerm x (ValPerm_LLVMBlock bp))
  | NameSet.member l (freeVars bp) =
    do Some lops <- lownedPermsForLifetime l perms
       return $ Some $ (lops :>: LOwnedPermBlock (PExpr_Var x) bp)
lownedPermsForLifetime l (perms :>: VarAndPerm x p)
  | Nothing <- testEquality x l
  , not (NameSet.member l $ freeVars p)
  = lownedPermsForLifetime l perms
lownedPermsForLifetime l (_ :>: vap) =
  fail $ renderDoc $ fillSep
  [pretty "lownedPermsForLifetime: could not compute lowned permissions for "
   <+> permPretty emptyPPInfo l <+> pretty "in:",
   permPretty emptyPPInfo vap]

-- | Get the 'String' name defined by a 'LifetimeDef'
lifetimeDefName :: LifetimeDef a -> String
lifetimeDefName (LifetimeDef _ (Lifetime name _) _ _) = name

extMbOuter :: RAssign prx ctx1 -> Mb ctx2 a -> Mb (ctx1 :++: ctx2) a
extMbOuter prxs mb_a = mbCombine $ nuMulti prxs $ const mb_a

-- | Add a lifetime described by a 'LifetimeDef' to a 'Some3FunPerm'
mbLifetimeFunPerm :: LifetimeDef Span -> Binding LifetimeType Some3FunPerm ->
                     RustConvM Some3FunPerm
mbLifetimeFunPerm (LifetimeDef _ _ [] _) [nuP| Some3FunPerm fun_perm |] =
  do let ghosts = mbLift $ fmap funPermGhosts fun_perm
     let args = mbLift $ fmap funPermArgs fun_perm
     let args_prxs = cruCtxProxies args
     let ret = mbLift $ fmap funPermRet fun_perm
     let mb_ps_in =
           mbCombineAssoc (MNil :>: Proxy) ghosts args_prxs $
           fmap (mbValuePermsToDistPerms . funPermIns) fun_perm
     let mb_ps_out =
           mbCombineAssoc (MNil :>: Proxy) ghosts (args_prxs :>: Proxy) $
           fmap (mbValuePermsToDistPerms . funPermOuts) fun_perm
     let mb_l =
           extMbMulti (cruCtxProxies args) $
           extMbMulti (cruCtxProxies ghosts) (nu id)
     [nuP| Some mb_lops_in |] <-
       mbM $ mbMap2 lownedPermsForLifetime mb_l mb_ps_in
     [nuP| Some mb_lops_out |] <-
       mbM $ mbMap2 lownedPermsForLifetime (extMb mb_l) mb_ps_out
     case abstractMbLOPsModalities mb_lops_in of
       SomeTypedMb ghosts' mb_mb_lops_in_abs ->
         return $ mbGhostsFunPerm3 ghosts' $
         flip fmap mb_mb_lops_in_abs $ \mb_lops_in_abs ->
         Some3FunPerm $ FunPerm (appendCruCtx
                                 (singletonCruCtx LifetimeRepr) ghosts) args ret
         (mbMap3 (\ps_in lops_in lops_in_abs ->
                   assocAppend (MNil :>: ValPerm_LOwned lops_in lops_in_abs)
                   ghosts args_prxs $ distPermsToValuePerms ps_in)
          mb_ps_in mb_lops_in mb_lops_in_abs)
         (mbMap3 (\ps_out lops_out lops_in_abs ->
                   assocAppend (MNil :>: ValPerm_LOwned lops_out lops_in_abs)
                   ghosts (args_prxs :>: Proxy) $ distPermsToValuePerms ps_out)
          mb_ps_out mb_lops_out (extMb mb_lops_in_abs))
mbLifetimeFunPerm (LifetimeDef _ _ _bounds _) [nuP| Some3FunPerm _fun_perm |] =
  fail "Rust lifetime bounds not yet supported!"

-- | Run a computation of a function permission in the context of a list of
-- Rust lifetime definitions
withLifetimes :: [LifetimeDef Span] -> RustConvM Some3FunPerm ->
                 RustConvM Some3FunPerm
withLifetimes [] m = m
withLifetimes (ldef : ldefs) m =
  inRustCtx (rustCtx1 (lifetimeDefName ldef)
             LifetimeRepr) (withLifetimes ldefs m) >>=
  mbLifetimeFunPerm ldef


-- | Convert a monomorphic function type, i.e., one with no type arguments
rsConvertMonoFun :: (1 <= w, KnownNat w) => prx w -> Span -> Abi ->
                    [LifetimeDef Span] -> FnDecl Span ->
                    RustConvM Some3FunPerm
rsConvertMonoFun w span abi ls fn_tp =
  rsConvertFun w abi (Generics ls [] (WhereClause [] span) span) fn_tp

-- | Convert a Rust polymorphic function type to a Heapster function permission
rsConvertFun :: (1 <= w, KnownNat w) => prx w ->
                Abi -> Generics Span -> FnDecl Span -> RustConvM Some3FunPerm
rsConvertFun w abi (Generics ldefs _tparams@[]
                    (WhereClause [] _) _) (FnDecl args (Just ret_tp) False _) =
  fmap (\ret ->
         tracePretty (pretty "rsConvertFun returning:" <+>
                      permPretty emptyPPInfo ret) ret) $
  withLifetimes ldefs $
  do arg_shapes <- mapM (rsConvert w) args
     ret_shape <- rsConvert w ret_tp
     layoutFun abi arg_shapes ret_shape


----------------------------------------------------------------------
-- * Top-level Entrypoints
----------------------------------------------------------------------

-- | Parse a polymorphic Rust function type of the form
--
-- > <generics> (T1,...,Tn) -> T
--
-- and convert it to a Heapster function permission
parseFunPermFromRust :: (MonadFail m, 1 <= w, KnownNat w) =>
                        PermEnv -> prx w -> CruCtx args -> TypeRepr ret ->
                        String -> m (SomeFunPerm args ret)
parseFunPermFromRust env w args ret str
  | Just i <- findIndex (== '>') str
  , (gen_str, fn_str) <- splitAt (i+1) str
  , Right (Generics rust_ls1 rust_tvars wc span) <-
      parse (inputStreamFromString gen_str)
  , Right (BareFn _ abi rust_ls2 fn_tp _) <-
      parse (inputStreamFromString fn_str) =
    runLiftRustConvM (mkRustConvInfo env) $
    do some_fun_perm <-
         rsConvertFun w abi (Generics
                             (rust_ls1 ++ rust_ls2) rust_tvars wc span) fn_tp
       un3SomeFunPerm args ret some_fun_perm

  | Just i <- findIndex (== '>') str
  , (gen_str, _) <- splitAt (i+1) str
  , Left err <- parse @(Generics Span) (inputStreamFromString gen_str) =
    fail ("Error parsing generics: " ++ show err)

  | Just i <- findIndex (== '>') str
  , (_, fn_str) <- splitAt (i+1) str
  , Left err <- parse @(Ty Span) (inputStreamFromString fn_str) =
    fail ("Error parsing generics: " ++ show err)
parseFunPermFromRust _ _ _ _ str =
    fail ("Malformed Rust type: " ++ str)


$(mkNuMatching [t| ArgLayout |])
$(mkNuMatching [t| Some3FunPerm |])
$(mkNuMatching [t| forall a. NuMatching a => SomeTypedMb a |])
