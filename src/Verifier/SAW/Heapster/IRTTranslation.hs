{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Verifier.SAW.Heapster.IRTTranslation (
  translateCompleteIRTTyVars,
  IRTVarTree(..), pattern IRTVar, IRTVarIdxs,
  translateCompleteIRTDesc,
  translateCompleteIRTDef,
  translateCompleteIRTFoldFun,
  translateCompleteIRTUnfoldFun,
  -- * Useful functions
  completeOpenTermTyped,
  listSortOpenTerm,
  askExprCtxTerms
  ) where

import Numeric.Natural
import Data.Foldable
import Data.Functor.Const
import Data.Reflection
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits

import Verifier.SAW.OpenTerm
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.SharedTerm

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.SAWTranslation


-- | "Complete" an 'OpenTerm' to a closed 'TypedTerm' or 'fail' on
-- type-checking error
-- TODO Move this to OpenTerm.hs?
completeOpenTermTyped :: SharedContext -> OpenTerm -> IO TypedTerm
completeOpenTermTyped sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM termM sc Nothing []

-- | Build an element of type ListSort from a list of types
-- TODO Move this to OpenTerm.hs?
listSortOpenTerm :: [OpenTerm] -> OpenTerm
listSortOpenTerm [] = ctorOpenTerm "Prelude.LS_Nil" []
listSortOpenTerm (tp:tps) =
  ctorOpenTerm "Prelude.LS_Cons" [tp, listSortOpenTerm tps]

-- | Get the result of applying 'exprCtxToTerms' to the current expression
-- translation context
-- TODO Move this to SAWTranslation.hs?
askExprCtxTerms :: TransInfo info => TransM info ctx [OpenTerm]
askExprCtxTerms = exprCtxToTerms <$> infoCtx <$> ask


----------------------------------------------------------------------
-- The monad for translating IRT type variables
----------------------------------------------------------------------

data IRTRecPermName args where
  IRTRecPermName :: NamedPermName ns args tp -> IRTRecPermName args

data IRTTyVarsTransCtx args ext =
  IRTTyVarsTransCtx
  {
    irtTRecPerm :: IRTRecPermName args,
    irtTArgsCtx :: RAssign (Const [OpenTerm]) args,
    irtTExtCtx  :: RAssign Proxy ext,
    irtTPermEnv :: PermEnv
  }

-- | The monad for translating IRT type variables
type IRTTyVarsTransM args ext =
  ReaderT (IRTTyVarsTransCtx args ext) (Either String)

runIRTTyVarsTransM :: PermEnv -> NamedPermName ns args tp -> CruCtx args ->
                      IRTTyVarsTransM args RNil a ->
                      Either String a
runIRTTyVarsTransM env npn_rec argsCtx m = runReaderT m ctx
  where args_trans = RL.map (\tp -> Const $ typeTransTypes $
                               runNilTypeTransM (translateClosed tp) env)
                            (cruCtxToTypes argsCtx)
        ctx = IRTTyVarsTransCtx (IRTRecPermName npn_rec) args_trans MNil env

-- | Run an IRT type variables translation computation in an extended context
inExtIRTTyVarsTransM :: IRTTyVarsTransM args (ext :> tp) a ->
                        IRTTyVarsTransM args ext a
inExtIRTTyVarsTransM = withReaderT $
  \ctx -> ctx { irtTExtCtx = irtTExtCtx ctx :>: Proxy }

-- | Combine a binding inside an @args :++: ext@ binding into a single
-- @args :++: ext'@ binding
irtTMbCombine ::
  forall args ext c a.
  Mb (args :++: ext) (Binding c a) ->
  IRTTyVarsTransM args ext (Mb (args :++: (ext :> c)) a)
irtTMbCombine x =
  do ext <- irtTExtCtx <$> ask
     return $
       mbCombine (ext :>: Proxy) $
       fmap (mbCombine RL.typeCtxProxies ) $
       mbSeparate @_ @args ext x

-- | Create an @args :++: ext@ binding
irtNus :: (RAssign Name args -> RAssign Name ext -> b) ->
          IRTTyVarsTransM args ext (Mb (args :++: ext) b)
irtNus f = 
  do args <- irtTArgsCtx <$> ask
     ext  <- irtTExtCtx  <$> ask
     return $ mbCombine ext (nus (RL.map (\_->Proxy) args) (nus ext . f))

-- | Turn an @args :++: ext@ binding into just an @args@ binding using
-- 'partialSubst'
irtTSubstExt :: (Substable PartialSubst a Maybe, NuMatching a) =>
                Mb (args :++: ext) a ->
                IRTTyVarsTransM args ext (Mb args a)
irtTSubstExt x =
  do ext <- irtTExtCtx <$> ask
     let x' = mbSwap ext (mbSeparate ext x)
         emptyPS = PartialSubst $ RL.map (\_ -> PSubstElem Nothing) ext
     args <- RL.map (const Proxy) . irtTArgsCtx <$> ask
     case give args (partialSubst emptyPS x') of
       Just x'' -> return x''
       Nothing -> throwError $ "non-array permission in a recursive perm body"
                               ++ " depends on an existential variable!"


----------------------------------------------------------------------
-- Trees for keeping track of IRT variable indices
----------------------------------------------------------------------

data IRTVarTree a = IRTVarsNil
                  | IRTVarsCons a (IRTVarTree a)
                  | IRTVarsAppend (IRTVarTree a) (IRTVarTree a)
                  | IRTVarsConcat [IRTVarTree a]
                  | IRTRecVar -- the recursive case
                  deriving (Show, Eq, Functor, Foldable, Traversable)

pattern IRTVar :: a -> IRTVarTree a
pattern IRTVar ix = IRTVarsCons ix IRTVarsNil

type IRTVarTreeShape = IRTVarTree ()
type IRTVarIdxs      = IRTVarTree Natural

-- | Fill in all the leaves of an 'IRTVarTree' with sequential indices
setIRTVarIdxs :: IRTVarTreeShape -> IRTVarIdxs
setIRTVarIdxs tree = evalState (mapM (\_ -> nextIdx) tree) 0
  where nextIdx :: State Natural Natural
        nextIdx = state (\i -> (i,i+1))


----------------------------------------------------------------------
-- Translating IRT type variables
----------------------------------------------------------------------

-- | Given the name of a recursive permission being defined and its argument
-- content, translate the permission's body to a SAW core list of its IRT type
-- variables and an 'IRTVarIdxs', which is used to get indices into the list
-- when calling 'translateCompleteIRTDesc'
translateCompleteIRTTyVars :: SharedContext -> PermEnv ->
                              NamedPermName ns args tp -> CruCtx args ->
                              Mb args (ValuePerm a) ->
                              IO (TypedTerm, IRTVarIdxs)
translateCompleteIRTTyVars sc env npn_rec args p =
  case runIRTTyVarsTransM env npn_rec args (valuePermIRTTyVars p) of
    Left err -> fail err
    Right (tps, ixs) ->
      do tm <- completeOpenTermTyped sc $
               runNilTypeTransM (lambdaExprCtx args $
                                  listSortOpenTerm <$> sequence tps) env
         return (tm, setIRTVarIdxs ixs)

-- | Get all IRT type variables in a value perm
valuePermIRTTyVars :: Mb (args :++: ext) (ValuePerm a) ->
                      IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                                IRTVarTreeShape)
valuePermIRTTyVars mb_p = case mbMatch mb_p of
  [nuMP| ValPerm_Eq _ |] -> return ([], IRTVarsNil)
  [nuMP| ValPerm_Or p1 p2 |] ->
    do (tps1, ixs1) <- valuePermIRTTyVars p1
       (tps2, ixs2) <- valuePermIRTTyVars p2
       return (tps1 ++ tps2, IRTVarsAppend ixs1 ixs2)
  [nuMP| ValPerm_Exists p |] ->
    do let tp = mbBindingType p
           tp_trans = typeTransTupleType <$> translateClosed tp
       pCbn <- irtTMbCombine p
       (tps, ixs) <- inExtIRTTyVarsTransM (valuePermIRTTyVars pCbn)
       return (tp_trans : tps, IRTVarsCons () ixs)
  [nuMP| ValPerm_Named npn args off |] ->
    namedPermIRTTyVars mb_p npn args off
  [nuMP| ValPerm_Var x _ |] ->
    irtTTranslateVar mb_p x
  [nuMP| ValPerm_Conj ps |] ->
    do (tps, ixs) <- unzip <$> mapM atomicPermIRTTyVars (mbList ps)
       return (concat tps, IRTVarsConcat ixs)

-- | Get all IRT type variables in a named permission application. The first
-- argument must be either 'ValPerm_Named' or 'Perm_NamedConj' applied to the
-- remaining arguments.
namedPermIRTTyVars :: forall args ext a tr ns args' tp.
                      (Translate TypeTransInfo args a (TypeTrans tr),
                       Substable PartialSubst a Maybe, NuMatching a) =>
                      Mb (args :++: ext) a ->
                      Mb (args :++: ext) (NamedPermName ns args' tp) ->
                      Mb (args :++: ext) (PermExprs args') ->
                      Mb (args :++: ext) (PermOffset tp) ->
                      IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                                IRTVarTreeShape)
namedPermIRTTyVars p npn args off =
  do IRTRecPermName npn_rec <- irtTRecPerm <$> ask
     npn_args <- irtNus (\ns _ -> namesToExprs ns)
     npn_off  <- irtNus (\_  _ -> NoPermOffset @tp)
     case mbMatch $ testNamedPermNameEq npn_rec <$> npn of
       [nuMP| Just (Refl, Refl, Refl) |] ->
         if npn_args == args && npn_off == off
         then return ([], IRTRecVar)
         else throwError $ "recursive permission applied to different"
                           ++ " arguments in its definition!"
       _ -> do env <- irtTPermEnv <$> ask
               case lookupNamedPerm env (mbLift npn) of
                 Just (NamedPerm_Defined dp) ->
                   valuePermIRTTyVars (mbMap2 (unfoldDefinedPerm dp) args off)
                 _ -> do p' <- irtTSubstExt p
                         let p_trans = typeTransTupleType <$> translate p'
                         return ([p_trans], IRTVar ())

-- | Return a singleton list with the type corresponding to the given variable
-- if the variable has a type translation - otherwise this function returns
-- the empty list. The first argument must be either 'PExpr_Var' or
-- @(\x -> 'ValPerm_Var' x off)@ applied to the second argument.
irtTTranslateVar :: (IsTermTrans tr, Translate TypeTransInfo args a tr,
                     Substable PartialSubst a Maybe, NuMatching a) =>
                    Mb (args :++: ext) a -> Mb (args :++: ext) (ExprVar tp) ->
                    IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                              IRTVarTreeShape)
irtTTranslateVar p x =
  do p' <- irtTSubstExt p
     let tm_trans = transTerms <$> translate p'
     -- because of 'irtTSubstExt' above, we know x must be a member of args,
     --  so we can safely look up its type translation
     argsCtx <- irtTArgsCtx <$> ask
     extCtx  <- irtTExtCtx  <$> ask
     let err _ = error "arguments to irtTTranslateVar do not match"
         memb = mbLift $ fmap (either id err . mbNameBoundP)
                              (mbSwap extCtx (mbSeparate extCtx x))
         tp_trans = getConst $ RL.get memb argsCtx
     -- if x (and thus also p) has no translation, return an empty list
     case tp_trans of
       [] -> return ([], IRTVarsNil)
       _  -> return ([tupleOfTypes <$> tm_trans], IRTVar ())

-- | Get all IRT type variables in an atomic perm
atomicPermIRTTyVars :: Mb (args :++: ext) (AtomicPerm a) ->
                       IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                                 IRTVarTreeShape)
atomicPermIRTTyVars mb_p = case mbMatch mb_p of
  [nuMP| Perm_LLVMField fld |] ->
    valuePermIRTTyVars (fmap llvmFieldContents fld)
  [nuMP| Perm_LLVMArray mb_ap |] ->
    do let mb_flds = fmap llvmArrayFields mb_ap
           flds = fmap (fmap llvmArrayFieldToAtomicPerm) (mbList mb_flds)
       (fld_tps, ixs) <- unzip <$> mapM atomicPermIRTTyVars flds
       return (concat fld_tps, IRTVarsConcat ixs)
  [nuMP| Perm_LLVMBlock bp |] ->
    shapeExprIRTTyVars (fmap llvmBlockShape bp)
  [nuMP| Perm_LLVMFree _ |] -> return ([], IRTVarsNil)
  [nuMP| Perm_LLVMFunPtr _ p |] ->
    valuePermIRTTyVars p
  [nuMP| Perm_IsLLVMPtr |] -> return ([], IRTVarsNil)
  [nuMP| Perm_LLVMBlockShape sh |] ->
    shapeExprIRTTyVars sh
  [nuMP| Perm_NamedConj npn args off |] ->
    namedPermIRTTyVars mb_p npn args off
  [nuMP| Perm_LLVMFrame _ |] -> return ([], IRTVarsNil)
  [nuMP| Perm_LOwned _ _ |] ->
    throwError "lowned permission in an IRT definition!"
  [nuMP| Perm_LCurrent _ |] -> return ([], IRTVarsNil)
  [nuMP| Perm_Struct ps |] -> valuePermsIRTTyVars ps
  [nuMP| Perm_Fun _ |] ->
    throwError "fun perm in an IRT definition!"
  [nuMP| Perm_BVProp _ |] ->
    throwError "BVProp in an IRT definition!"

-- | Get all IRT type variables in a shape expression
shapeExprIRTTyVars :: Mb (args :++: ext) (PermExpr (LLVMShapeType w)) ->
                      IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                                IRTVarTreeShape)
shapeExprIRTTyVars mb_p = case mbMatch mb_p of
  [nuMP| PExpr_Var x |] -> irtTTranslateVar mb_p x
  [nuMP| PExpr_EmptyShape |] -> return ([], IRTVarsNil)
  [nuMP| PExpr_EqShape _ |] -> return ([], IRTVarsNil)
  [nuMP| PExpr_PtrShape _ _ sh |] ->
      shapeExprIRTTyVars sh
  [nuMP| PExpr_FieldShape fsh |] ->
      fieldShapeIRTTyVars fsh
  [nuMP| PExpr_ArrayShape _ _ fshs |] ->
    do (tps, ixs) <- unzip <$> mapM fieldShapeIRTTyVars (mbList fshs)
       return (concat tps, IRTVarsConcat ixs)
  [nuMP| PExpr_SeqShape sh1 sh2 |] ->
    do (tps1, ixs1) <- shapeExprIRTTyVars sh1
       (tps2, ixs2) <- shapeExprIRTTyVars sh2
       return (tps1 ++ tps2, IRTVarsAppend ixs1 ixs2)
  [nuMP| PExpr_OrShape sh1 sh2 |] ->
    do (tps1, ixs1) <- shapeExprIRTTyVars sh1
       (tps2, ixs2) <- shapeExprIRTTyVars sh2
       return (tps1 ++ tps2, IRTVarsAppend ixs1 ixs2)
  [nuMP| PExpr_ExShape mb_sh |] ->
    do let tp = mbBindingType mb_sh
           tp_trans = typeTransTupleType <$> translateClosed tp
       shCbn <- irtTMbCombine mb_sh
       (tps, ixs) <- inExtIRTTyVarsTransM (shapeExprIRTTyVars shCbn)
       return (tp_trans : tps, IRTVarsCons () ixs)

-- | Get all IRT type variables in a field shape
fieldShapeIRTTyVars :: Mb (args :++: ext) (LLVMFieldShape w) ->
                       IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                                 IRTVarTreeShape)
fieldShapeIRTTyVars (mbMatch -> [nuMP| LLVMFieldShape p |]) =
  valuePermIRTTyVars p

-- | Get all IRT type variables in a set of value perms
valuePermsIRTTyVars :: Mb (args :++: ext) (ValuePerms ps) ->
                       IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                                 IRTVarTreeShape)
valuePermsIRTTyVars mb_ps = case mbMatch mb_ps of
  [nuMP| ValPerms_Nil |] -> return ([], IRTVarsNil)
  [nuMP| ValPerms_Cons ps p |] ->
    do (tps1, ixs1) <- valuePermsIRTTyVars ps
       (tps2, ixs2) <- valuePermIRTTyVars p
       return (tps1 ++ tps2, IRTVarsAppend ixs1 ixs2)


----------------------------------------------------------------------
-- The IRTDesc translation monad
----------------------------------------------------------------------

-- | Contextual info for translating IRT type descriptions
data IRTDescTransInfo ctx =
  IRTDescTransInfo { irtDExprCtx :: ExprTransCtx ctx,
                     irtDPermEnv :: PermEnv,
                     irtDTyVars  :: OpenTerm
                   }

-- | Build an empty 'IRTDescTransInfo' from a 'PermEnv' and type var 'Ident',
-- setting 'irtDTyVars' to 'globalOpenTerm' of the given 'Ident'
emptyIRTDescTransInfo :: PermEnv -> Ident -> IRTDescTransInfo RNil
emptyIRTDescTransInfo env tyVarsIdent =
  IRTDescTransInfo MNil env (globalOpenTerm tyVarsIdent)

-- | Apply the current 'irtDTyVars' to the current context using
-- 'applyOpenTermMulti' - intended to be used only in the args context and
-- when the trans info is 'emptyIRTDescTransInfo' (see its usage in
-- 'translateCompleteIRTDesc').
-- The result of calling this function appropriately is that 'irtDTyVars' now
-- contains a term which is the type variables identifier applied to its
-- arguments, no matter how much 'IRTDescTransM's context is extended. This
-- term is then used whenever an IRTDesc constructor is applied, see
-- 'irtCtorOpenTerm' and 'irtCtor'.
irtDInArgsCtx :: IRTDescTransM args OpenTerm -> IRTDescTransM args OpenTerm
irtDInArgsCtx m =
  do args <- askExprCtxTerms
     flip local m $ \info ->
       info { irtDTyVars = applyOpenTermMulti (irtDTyVars info) args }

instance TransInfo IRTDescTransInfo where
  infoCtx = irtDExprCtx
  infoEnv = irtDPermEnv
  extTransInfo etrans (IRTDescTransInfo {..}) =
    IRTDescTransInfo
    { irtDExprCtx = irtDExprCtx :>: etrans
    , .. }

-- | The monad for translating IRT type descriptions
type IRTDescTransM = TransM IRTDescTransInfo

-- | Apply the given IRT constructor to the given arguments, using the
-- type variable identifier applied to its arguments from the current
-- 'IRTDescTransInfo' for the first argument
irtCtorOpenTerm :: Ident -> [OpenTerm] -> IRTDescTransM ctx OpenTerm
irtCtorOpenTerm c all_args =
  do tyVarsTm <- irtDTyVars <$> ask
     return $ ctorOpenTerm c (tyVarsTm : all_args)

-- | Like 'tupleOfTypes' but with @IRT_prod@
irtProd :: [OpenTerm] -> IRTDescTransM ctx OpenTerm
irtProd [x] = return x
irtProd xs =
  do irtUnit <- irtCtorOpenTerm "Prelude.IRT_unit" []
     foldrM (\x xs' -> irtCtorOpenTerm "Prelude.IRT_prod" [x, xs'])
            irtUnit xs

-- | A singleton list containing the result of 'irtCtorOpenTerm'
irtCtor :: Ident -> [OpenTerm] -> IRTDescTransM ctx [OpenTerm]
irtCtor c all_args =
  do tm <- irtCtorOpenTerm c all_args
     return [tm]


----------------------------------------------------------------------
-- Translating IRT type descriptions
----------------------------------------------------------------------

-- | Given an identifier whose definition in the shared context is the first
-- result of calling 'translateCompleteIRTTyVars' on the same argument context
-- and recursive permission body given here, and an 'IRTVarIdxs' which is the
-- second result of the same call to 'translateCompleteIRTTyVars', translate
-- the given recursive permission body to an IRT type description
translateCompleteIRTDesc :: SharedContext -> PermEnv -> 
                            Ident -> CruCtx args ->
                            Mb args (ValuePerm a) -> IRTVarIdxs ->
                            IO TypedTerm
translateCompleteIRTDesc sc env tyVarsIdent args p ixs =
  do tm <- completeOpenTerm sc $
           runTransM (lambdaExprCtx args . irtDInArgsCtx $
                        do in_mu <- valuePermIRTDesc p ixs >>= irtProd
                           irtCtorOpenTerm "Prelude.IRT_mu" [in_mu])
                     (emptyIRTDescTransInfo env tyVarsIdent)
     -- we manually give the type because we want to keep 'tyVarsIdent' folded
     let irtDescOpenTerm ectx = return $
           dataTypeOpenTerm "Prelude.IRTDesc"
             [ applyOpenTermMulti (globalOpenTerm tyVarsIdent)
                                  (exprCtxToTerms ectx) ]
     tp <- completeOpenTerm sc $
           runNilTypeTransM (translateClosed args >>= \tptrans ->
                              piTransM "e" tptrans irtDescOpenTerm) env
     return $ TypedTerm tm tp

-- | Get the IRTDescs associated to a value perm. Apply 'irtProd' to
-- the results to get the single IRTDesc to which the input corresponds.
valuePermIRTDesc :: Mb ctx (ValuePerm a) -> IRTVarIdxs ->
                    IRTDescTransM ctx [OpenTerm]
valuePermIRTDesc mb_p ixs = case (mbMatch mb_p, ixs) of
  ([nuMP| ValPerm_Eq _ |], _) -> return []
  ([nuMP| ValPerm_Or p1 p2 |], IRTVarsAppend ixs1 ixs2) ->
    do x1 <- valuePermIRTDesc p1 ixs1 >>= irtProd
       x2 <- valuePermIRTDesc p2 ixs2 >>= irtProd
       irtCtor "Prelude.IRT_Either" [x1, x2]
  ([nuMP| ValPerm_Exists p |], IRTVarsCons ix ixs') ->
    do let tp = mbBindingType p
       tp_trans <- tupleTypeTrans <$> translateClosed tp
       xf <- lambdaTransM "x_irt" tp_trans (\x -> inExtTransM x $
               valuePermIRTDesc (mbCombine RL.typeCtxProxies p) ixs' >>= irtProd)
       irtCtor "Prelude.IRT_sigT" [natOpenTerm ix, xf]
  ([nuMP| ValPerm_Named npn args off |], _) ->
    namedPermIRTDesc npn args off ixs
  ([nuMP| ValPerm_Var _ _ |], _) -> irtVarT ixs
  ([nuMP| ValPerm_Conj ps |], IRTVarsConcat ixss) ->
    concat <$> zipWithM atomicPermIRTDesc (mbList ps) ixss
  _ -> error $ "malformed IRTVarIdxs: " ++ show ixs

-- | Get the IRTDescs associated to a named perm. Apply 'irtProd' to
-- the results to get the single IRTDesc to which the input corresponds.
namedPermIRTDesc :: Mb ctx (NamedPermName ns args tp) ->
                    Mb ctx (PermExprs args) ->
                    Mb ctx (PermOffset tp) -> IRTVarIdxs ->
                    IRTDescTransM ctx [OpenTerm]
namedPermIRTDesc npn args off ixs = case ixs of
  IRTRecVar -> irtCtor "Prelude.IRT_varD" [natOpenTerm 0]
  _ -> do env <- infoEnv <$> ask
          case (lookupNamedPerm env (mbLift npn), ixs) of
            (Just (NamedPerm_Defined dp), _) ->
              valuePermIRTDesc (mbMap2 (unfoldDefinedPerm dp) args off) ixs
            (_, IRTVar ix) -> irtCtor "Prelude.IRT_varT" [natOpenTerm ix]
            _ -> error $ "malformed IRTVarIdxs: " ++ show ixs

-- | Get the IRTDescs associated to a variable. Apply 'irtProd' to
-- the results to get the single IRTDesc to which the input corresponds.
irtVarT :: IRTVarIdxs -> IRTDescTransM ctx [OpenTerm]
irtVarT ixs = case ixs of
  IRTVarsNil -> return []
  IRTVar ix -> irtCtor "Prelude.IRT_varT" [natOpenTerm ix]
  _ -> error $ "malformed IRTVarIdxs: " ++ show ixs

-- | Get the IRTDescs associated to an atomic perm. Apply 'irtProd' to
-- the results to get the single IRTDesc to which the input corresponds.
atomicPermIRTDesc :: Mb ctx (AtomicPerm a) -> IRTVarIdxs ->
                     IRTDescTransM ctx [OpenTerm]
atomicPermIRTDesc mb_p ixs = case (mbMatch mb_p, ixs) of
  ([nuMP| Perm_LLVMField fld |], _) ->
    valuePermIRTDesc (fmap llvmFieldContents fld) ixs
  ([nuMP| Perm_LLVMArray mb_ap |], IRTVarsConcat ixss) ->
    do let w = natVal2 mb_ap
           w_term = natOpenTerm w
           mb_len = fmap llvmArrayLen mb_ap
           mb_flds = fmap llvmArrayFields mb_ap
           flds = fmap (fmap llvmArrayFieldToAtomicPerm) (mbList mb_flds)
       len_term <- translate1 mb_len
       xs <- concat <$> zipWithM atomicPermIRTDesc flds ixss
       xs_term <- irtProd xs
       irtCtor "Prelude.IRT_BVVec" [w_term, len_term, xs_term]
  ([nuMP| Perm_LLVMBlock bp |], _) ->
    shapeExprIRTDesc (fmap llvmBlockShape bp) ixs
  ([nuMP| Perm_LLVMFree _ |], _) -> return []
  ([nuMP| Perm_LLVMFunPtr _ p |], _) ->
    valuePermIRTDesc p ixs
  ([nuMP| Perm_IsLLVMPtr |], _) -> return []
  ([nuMP| Perm_LLVMBlockShape sh |], _) ->
    shapeExprIRTDesc sh ixs
  ([nuMP| Perm_NamedConj npn args off |], _) ->
    namedPermIRTDesc npn args off ixs
  ([nuMP| Perm_LLVMFrame _ |], _) -> return []
  ([nuMP| Perm_LOwned _ _ |], _) ->
    error "lowned permission made it to IRTDesc translation"
  ([nuMP| Perm_LCurrent _ |], _) -> return []
  ([nuMP| Perm_Struct ps |], _) ->
    valuePermsIRTDesc ps ixs
  ([nuMP| Perm_Fun _ |], _) ->
    error "fun perm made it to IRTDesc translation"
  ([nuMP| Perm_BVProp _ |], _) ->
    error "BVProp made it to IRTDesc translation"
  _ -> error $ "malformed IRTVarIdxs: " ++ show ixs

-- | Get the IRTDescs associated to a shape expression. Apply 'irtProd' to
-- the results to get the single IRTDesc to which the input corresponds.
shapeExprIRTDesc :: Mb ctx (PermExpr (LLVMShapeType w)) -> IRTVarIdxs ->
                    IRTDescTransM ctx [OpenTerm]
shapeExprIRTDesc mb_expr ixs = case (mbMatch mb_expr, ixs) of
  ([nuMP| PExpr_EmptyShape |], _) -> return []
  ([nuMP| PExpr_EqShape _ |], _) -> return []
  ([nuMP| PExpr_PtrShape _ _ sh |], _) ->
    shapeExprIRTDesc sh ixs
  ([nuMP| PExpr_FieldShape fsh |], _) ->
    fieldShapeIRTDesc fsh ixs
  ([nuMP| PExpr_ArrayShape mb_len _ mb_fshs |], IRTVarsConcat ixss) ->
    do let w = natVal4 mb_len
       let w_term = natOpenTerm w
       len_term <- translate1 mb_len
       xs <- concat <$> zipWithM fieldShapeIRTDesc (mbList mb_fshs) ixss
       xs_term <- irtProd xs
       irtCtor "Prelude.IRT_BVVec" [w_term, len_term, xs_term]
  ([nuMP| PExpr_SeqShape sh1 sh2 |], IRTVarsAppend ixs1 ixs2) ->
    do x1 <- shapeExprIRTDesc sh1 ixs1 >>= irtProd
       x2 <- shapeExprIRTDesc sh2 ixs2 >>= irtProd
       irtCtor "Prelude.IRT_prod" [x1, x2]
  ([nuMP| PExpr_OrShape sh1 sh2 |], IRTVarsAppend ixs1 ixs2) ->
    do x1 <- shapeExprIRTDesc sh1 ixs1 >>= irtProd
       x2 <- shapeExprIRTDesc sh2 ixs2 >>= irtProd
       irtCtor "Prelude.IRT_Either" [x1, x2]
  ([nuMP| PExpr_ExShape mb_sh |], IRTVarsCons ix ixs') ->
    do let tp = mbBindingType mb_sh
       tp_trans <- tupleTypeTrans <$> translateClosed tp
       xf <- lambdaTransM "x_irt" tp_trans (\x -> inExtTransM x $
               shapeExprIRTDesc (mbCombine RL.typeCtxProxies mb_sh) ixs' >>= irtProd)
       irtCtor "Prelude.IRT_sigT" [natOpenTerm ix, xf]
  _ -> error $ "malformed IRTVarIdxs: " ++ show ixs

-- | Get the IRTDescs associated to a field shape. Apply 'irtProd' to
-- the results to get the single IRTDesc to which the input corresponds.
fieldShapeIRTDesc :: Mb ctx (LLVMFieldShape w) -> IRTVarIdxs ->
                     IRTDescTransM ctx [OpenTerm]
fieldShapeIRTDesc (mbMatch -> [nuMP| LLVMFieldShape p |]) ixs =
  valuePermIRTDesc p ixs

-- | Get the IRTDescs associated to a set of value perms. Apply 'irtProd' to
-- the results to get the single IRTDesc to which the input corresponds.
valuePermsIRTDesc :: Mb ctx (ValuePerms ps) -> IRTVarIdxs ->
                     IRTDescTransM ctx [OpenTerm]
valuePermsIRTDesc mb_ps ixs = case (mbMatch mb_ps, ixs) of
  ([nuMP| ValPerms_Nil |], _) -> return []
  ([nuMP| ValPerms_Cons ps p |], IRTVarsAppend ixs1 ixs2) ->
    do xs <- valuePermsIRTDesc ps ixs1
       x  <- valuePermIRTDesc p ixs2
       return $ xs ++ x
  _ -> error $ "malformed IRTVarIdxs: " ++ show ixs


----------------------------------------------------------------------
-- Translating IRT definitions
----------------------------------------------------------------------

-- | Given identifiers whose definitions in the shared context are the results
-- of corresponding calls to 'translateCompleteIRTTyVars' and
-- 'translateCompleteIRTDesc', return a term which is @IRT@ applied to these
-- identifiers
translateCompleteIRTDef :: SharedContext -> PermEnv -> 
                           Ident -> Ident -> CruCtx args ->
                           IO TypedTerm
translateCompleteIRTDef sc env tyVarsIdent descIdent args =
  completeOpenTermTyped sc $
  runNilTypeTransM (lambdaExprCtx args $
                     irtDefinition tyVarsIdent descIdent) env

-- | Given identifiers whose definitions in the shared context are the results
-- of corresponding calls to 'translateCompleteIRTTyVars',
-- 'translateCompleteIRTDesc', and 'translateCompleteIRTDef', return a term
-- which is @foldIRT@ applied to these identifiers
translateCompleteIRTFoldFun :: SharedContext -> PermEnv -> 
                               Ident -> Ident -> Ident -> CruCtx args ->
                               IO Term
translateCompleteIRTFoldFun sc env tyVarsIdent descIdent _ args =
  completeOpenTerm sc $
  runNilTypeTransM (lambdaExprCtx args $
                     irtFoldFun tyVarsIdent descIdent) env

-- | Given identifiers whose definitions in the shared context are the results
-- of corresponding calls to 'translateCompleteIRTTyVars',
-- 'translateCompleteIRTDesc', and 'translateCompleteIRTDef', return a term
-- which is @foldIRT@ applied to these identifiers
translateCompleteIRTUnfoldFun :: SharedContext -> PermEnv -> 
                                 Ident -> Ident -> Ident -> CruCtx args ->
                                 IO Term
translateCompleteIRTUnfoldFun sc env tyVarsIdent descIdent _ args =
  completeOpenTerm sc $
  runNilTypeTransM (lambdaExprCtx args $
                     irtUnfoldFun tyVarsIdent descIdent) env

-- | Get the terms for the arguments to @IRT@, @foldIRT@, and @unfoldIRT@
-- given the appropriate identifiers
irtDefArgs :: Ident -> Ident -> TypeTransM args (OpenTerm, OpenTerm, OpenTerm)
irtDefArgs tyVarsIdent descIdent = 
  do args <- askExprCtxTerms
     let tyVars = applyOpenTermMulti (globalOpenTerm tyVarsIdent) args
         substs = ctorOpenTerm "Prelude.IRTs_Nil" [tyVars]
         desc   = applyOpenTermMulti (globalOpenTerm descIdent) args
     return (tyVars, substs, desc)

irtDefinition :: Ident -> Ident -> TypeTransM args OpenTerm
irtDefinition tyVarsIdent descIdent = 
  do (tyVars, substs, desc) <- irtDefArgs tyVarsIdent descIdent
     return $ dataTypeOpenTerm "Prelude.IRT" [tyVars, substs, desc]

irtFoldFun :: Ident -> Ident -> TypeTransM args OpenTerm
irtFoldFun tyVarsIdent descIdent = 
  do (tyVars, substs, desc) <- irtDefArgs tyVarsIdent descIdent
     return $ applyOpenTermMulti (globalOpenTerm "Prelude.foldIRT")
                                 [tyVars, substs, desc]

irtUnfoldFun :: Ident -> Ident -> TypeTransM args OpenTerm
irtUnfoldFun tyVarsIdent descIdent = 
  do (tyVars, substs, desc) <- irtDefArgs tyVarsIdent descIdent
     return $ applyOpenTermMulti (globalOpenTerm "Prelude.unfoldIRT")
                                 [tyVars, substs, desc]
