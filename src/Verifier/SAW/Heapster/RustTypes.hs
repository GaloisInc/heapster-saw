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

import Data.Maybe
import GHC.TypeLits
import Data.Functor.Constant
import Data.Functor.Product
import Control.Monad.Reader
import Control.Monad.Except

import Data.Parameterized.Some

import Data.Binding.Hobbits
import Data.Binding.Hobbits.MonadBind
import Data.Type.RList (RList(..), RAssign(..), (:++:), append, memberElem,
                        mapRAssign, mapToList)
import qualified Data.Type.RList as RL

import Language.Rust.Syntax
import Language.Rust.Parser
import Language.Rust.Data.Ident (Ident(..))

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
                 rciLifetime :: PermExpr LifetimeType,
                 rciRW :: PermExpr RWModalityType,
                 rciCtx :: [(String, TypedName)] }

-- | The default, top-level 'RustConvInfo' for a given 'PermEnv'
mkRustConvInfo :: PermEnv -> RustConvInfo
mkRustConvInfo env =
  RustConvInfo { rciPermEnv = env, rciLifetime = PExpr_Always,
                 rciRW = PExpr_Write, rciCtx = [] }

-- | The Rust conversion monad is just a state-error monad
newtype RustConvM a =
  RustConvM { unRustConvM :: ReaderT RustConvInfo (Except String) a }
  deriving (Functor, Applicative, Monad,
            MonadError String, MonadReader RustConvInfo)

instance MonadFail RustConvM where
  fail = RustConvM . throwError

instance (MonadBind m, Liftable e) => MonadBind (ExceptT e m) where
  mbM mb_m =
    ExceptT $
    do mb_eith <- mbM $ fmap runExceptT mb_m
       case mb_eith of
         [nuP| Right mb_a |] -> return $ Right mb_a
         [nuP| Left mb_e |] -> return $ Left $ mbLift mb_e

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

-- | A context of Rust type and lifetime variables
type RustCtx = RAssign (Product (Constant String) TypeRepr)

-- | Extract a 'CruCtx' from a 'RustCtx'
rustCtxCtx :: RustCtx ctx -> CruCtx ctx
rustCtxCtx = cruCtxOfTypes . RL.map (\(Pair _ tp) -> tp)

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

-- | A shape function with existentially quantified arguments
data SomeShapeFun w =
  forall args. SomeShapeFun (CruCtx args) (Mb args (PermExpr (LLVMShapeType w)))

-- | A sequence of 'PermExprs' along with their types
data TypedPermExprs ctx = TypedPermExprs (CruCtx ctx) (PermExprs ctx)

-- | Apply a 'SomeShapeFun', if possible
tryApplySomeShapeFun :: SomeShapeFun w -> Some TypedPermExprs ->
                        Maybe (PermExpr (LLVMShapeType w))
tryApplySomeShapeFun (SomeShapeFun ctx mb_sh) (Some (TypedPermExprs ctx' args))
  | Just Refl <- testEquality ctx ctx' =
    Just $ subst (substOfExprs args) mb_sh
tryApplySomeShapeFun _ _ = Nothing

-- | Build the shape @fieldsh(exists z:bv sz.eq(llvmword(z))@
sizedIntShapeFun :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                    prx1 w -> prx2 sz -> SomeShapeFun w
sizedIntShapeFun _ (_ :: prx2 sz) =
  SomeShapeFun CruCtxNil $ emptyMb $
  PExpr_FieldShape (LLVMFieldShape $ ValPerm_Exists $ nu $
                    \(z :: ExprVar (BVType sz)) ->
                     ValPerm_Eq (PExpr_LLVMWord (PExpr_Var z)))

-- | A table for converting Rust base types to shapes
namedTypeTable :: (1 <= w, KnownNat w) => prx w -> [(String,SomeShapeFun w)]
namedTypeTable w =
  [("bool", sizedIntShapeFun @_ @1 w Proxy)]

-- | A fully qualified Rust path without any of the parameters; e.g.,
-- @Foo<X>::Bar<Y,Z>::Baz@ just becomes @[Foo,Bar,Baz]@
newtype RustName = RustName [Ident]

instance RsConvert w RustName (SomeShapeFun w) where
  rsConvert w (RustName elems) =
    -- FIXME: figure out how to actually resolve names; for now we just look at
    -- the last string component...
    let str = name $ last elems in
    -- FIXME: write this in a nice monadic way...
    case lookup str (namedTypeTable w) of
      Just shf -> return shf
      Nothing ->
        do env <- rciPermEnv <$> ask
           case lookupNamedShape env str of
             Just (SomeNamedShape _ args mb_sh)
               | LLVMShapeRepr w' <- mbLift $ fmap exprType mb_sh
               , Just Refl <- testEquality (natRepr w) w' ->
                 return $ SomeShapeFun args mb_sh
             Just _ -> fail ("Named Rust type of wrong shape width: " ++ str)
             Nothing ->
               fail ("Could not find translation of Rust type name: " ++ str)

-- | Get the "name" = sequence of identifiers out of a Rust path
rsPathName :: Path a -> RustName
rsPathName (Path _ segments _) =
  RustName $ map (\(PathSegment rust_id _ _) -> rust_id) segments

-- | Get all the parameters out of a Rust path
rsPathParams :: Path a -> [PathParameters a]
rsPathParams (Path _ segments _) =
  mapMaybe (\(PathSegment _ maybe_params _) -> maybe_params) segments


----------------------------------------------------------------------
-- * Converting Rust Types
----------------------------------------------------------------------

instance RsConvert w Mutability (PermExpr RWModalityType) where
  rsConvert _ Mutable = return PExpr_Write
  rsConvert _ Immutable = return PExpr_Read

instance RsConvert w (Lifetime Span) (PermExpr LifetimeType) where
  rsConvert _ (Lifetime "static" span) = return PExpr_Always
  rsConvert _ (Lifetime l span) =
    PExpr_Var <$> atSpan span (lookupName l knownRepr)

instance RsConvert w (Generics Span) (Some RustCtx) where
  rsConvert _ _ = error "FIXME HERE"

typedExprsOfList :: TypeRepr a -> [PermExpr a] -> Some TypedPermExprs
typedExprsOfList = error "FIXME HERE"

appendTypedExprs :: Some TypedPermExprs -> Some TypedPermExprs ->
                    Some TypedPermExprs
appendTypedExprs = error "FIXME HERE"

instance RsConvert w (PathParameters Span) (Some TypedPermExprs) where
  rsConvert w (AngleBracketed rust_ls rust_tps [] _) =
    do ls <- mapM (rsConvert w) rust_ls
       shs <- mapM (rsConvert w) rust_tps
       return $ appendTypedExprs
         (typedExprsOfList knownRepr ls) (typedExprsOfList knownRepr shs)

instance RsConvert w [PathParameters Span] (Some TypedPermExprs) where
  rsConvert _ _ = error "FIXME HERE"

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
    do sh_f <- rsConvert w (rsPathName path)
       args <- rsConvert w (rsPathParams path)
       case tryApplySomeShapeFun sh_f args of
         Just sh -> return sh
         Nothing -> fail "Argument types not as expected"
  rsConvert w (BareFn _ _ _ _ _) =
    error "FIXME HERE: translate function types!"
  rsConvert _ tp = fail ("Rust type not supported: " ++ show tp)

-- | Convert a Rust type to a shape and test if that shape has a single field,
-- i.e., is of the form @ptrsh(p)@. If so, return @p@, and otherwise fail. The
-- first argument is the width of pointer values on this architecture.
rustTypeToPerm :: (1 <= w, KnownNat w) => prx w -> Ty Span ->
                  RustConvM SomeLLVMPerm
rustTypeToPerm w tp =
  rsConvert w tp >>= \case
  PExpr_FieldShape (LLVMFieldShape p) -> return (SomeLLVMPerm p)
  _ -> fail ("Rust type is not a valid argument type: " ++ show tp)


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
parseFunPermFromRust env w args ret str =
  case execParser ((,) <$> parser <*> parser)
       (inputStreamFromString str) initPos of
    Left err -> fail $ show err
    Right (generics :: Generics Span, rust_tp) ->
      runLiftRustConvM (mkRustConvInfo env) $
      do Some rust_ctx <- rsConvert w generics
         mb_some_perm <- inRustCtx rust_ctx $ rustTypeToPerm w rust_tp
         case mb_some_perm of
           [nuP| SomeLLVMPerm
                  (ValPerm_Conj1
                   (Perm_LLVMFunPtr (FunctionHandleRepr args' ret')
                    (ValPerm_Conj1 (Perm_Fun fun_perm)))) |]
             | Just Refl <- testEquality (mkCruCtx $ mbLift args') args
             , Just Refl <- testEquality (mbLift ret') ret ->
               return (SomeFunPerm $ mbFunPerm (rustCtxCtx rust_ctx) fun_perm)
           _ -> fail "FIXME: better error message!"
