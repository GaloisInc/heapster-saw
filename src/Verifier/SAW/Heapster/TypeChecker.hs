{-# Language GADTs #-}
{-# Language BlockArguments #-}
{-# Language RankNTypes #-}
{-# Language TemplateHaskell #-}
{-# Language TypeOperators #-}
{-# Language DataKinds #-}
{-# Language ImportQualifiedPost #-}
module Verifier.SAW.Heapster.TypeChecker where

import Data.Functor.Product
import Data.Functor.Constant
import GHC.TypeLits (KnownNat)
import GHC.Natural

import Data.Binding.Hobbits

import Data.Parameterized.Some (Some(Some), mapSome)
import Data.Parameterized.Context qualified as Ctx

import Lang.Crucible.Types

import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Located
import Verifier.SAW.Heapster.UntypedAST

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

tcCastTyped :: Pos -> String -> TypeRepr a -> Some (Typed f) -> Tc (f a)
tcCastTyped _ _ tp (Some (Typed tp' f))
  | Just Refl <- testEquality tp tp' = pure f
tcCastTyped p str tp (Some (Typed tp' _)) =
  tcError p ("Expected " ++ str ++ " of type " ++ show tp
        ++ ", found one of type " ++ show tp')

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

tcExpr :: TypeRepr a -> AstExpr -> Tc (PermExpr a)
tcExpr ty (ExVar p name args offset) =
  do env <- tcAsk
     case lookupExprVar name env of
       Nothing -> tcError p "unknown variable"
       Just tn -> PExpr_Var <$> tcCastTyped p "variable" ty tn
