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
{-# LANGUAGE LambdaCase #-}

module Verifier.SAW.Heapster.IRTTranslation (
  translateCompleteIRTTyVars,
  translateCompleteIRTDesc
  ) where

import Numeric.Natural
import Control.Monad.Fail
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits
import Data.Binding.Hobbits.Liftable()
import Data.Binding.Hobbits.Mb (extMb, mbMap2)

import Lang.Crucible.Types

import Verifier.SAW.OpenTerm
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.SharedTerm

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.SAWTranslation


-- | "Complete" an 'OpenTerm' to a closed 'TypedTerm' or 'fail' on
-- type-checking error
completeOpenTermTyped :: SharedContext -> OpenTerm -> IO TypedTerm
completeOpenTermTyped sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM termM sc Nothing []

-- | Build an element of type ListSort from a list of types
listSortOpenTerm :: [OpenTerm] -> OpenTerm
listSortOpenTerm [] = ctorOpenTerm "Prelude.LS_Nil" []
listSortOpenTerm (tp:tps) =
  ctorOpenTerm "Prelude.LS_Cons" [tp, listSortOpenTerm tps]


----------------------------------------------------------------------
-- The monad for translating IRT type variables
----------------------------------------------------------------------

data IRTTyVarsTransCtx args ext where
  IRTTyVarsTransCtx :: { irtTRecPerm :: NamedPermName ns args tp
                       , irtTArgsCtx :: RAssign Proxy args
                       , irtTExtCtx  :: RAssign Proxy ext } ->
                       IRTTyVarsTransCtx args ext

-- | The monad for translating IRT type variables
type IRTTyVarsTransM args ext =
  ReaderT (IRTTyVarsTransCtx args ext)
          (StateT Natural (ExceptT String (TypeTransM args)))

runIRTTyVarsTransM :: NamedPermName ns args tp -> CruCtx args ->
                      IRTTyVarsTransM args RNil a ->
                      TypeTransM args (Either String a)
runIRTTyVarsTransM npn_rec args m =
  runExceptT (evalStateT (runReaderT m ctx) 0)
  where ctx = IRTTyVarsTransCtx npn_rec (cruCtxProxies args) MNil

-- | Run a regular translation computation in an IRT type variables
-- translation computation
liftIRTTyVarsTransM :: TypeTransM args a -> IRTTyVarsTransM args ext a
liftIRTTyVarsTransM = lift . lift . lift

irtTNextIndex :: IRTTyVarsTransM args ext Natural
irtTNextIndex = state (\i -> (i, i+1))

-- | Run an IRT type variables translation computation in an extended context
inExtIRTTyVarsTransM :: IRTTyVarsTransM args (ext :> tp) a ->
                        IRTTyVarsTransM args ext a
inExtIRTTyVarsTransM = withReaderT $
  \ctx -> ctx { irtTExtCtx = irtTExtCtx ctx :>: Proxy }

-- | Combine a binding inside an @args :++: ext@ binding into a single
-- @args :++: ext'@ binding
irtTMbCombine :: forall args ext ctx a.
                 Mb (args :++: ext) (Mb ctx a) ->
                 IRTTyVarsTransM args ext (Mb (args :++: (ext :++: ctx)) a)
irtTMbCombine x =
  do ext <- irtTExtCtx <$> ask
     return $ mbCombine (fmap mbCombine (mbSeparate @_ @args ext x))

-- | Turn an @args :++: ext@ binding into just an @args@ binding using
-- 'partialSubst'
irtTSubstExt :: (Substable PartialSubst a Maybe, NuMatching a) =>
                Mb (args :++: ext) a ->
                IRTTyVarsTransM args ext (Mb args a)
irtTSubstExt x =
  do ext <- irtTExtCtx <$> ask
     let x' = mbSwap (mbSeparate ext x)
         emptyPS = PartialSubst $ RL.map (\_ -> PSubstElem Nothing) ext
     case partialSubst emptyPS x' of
       Just x'' -> return x''
       Nothing -> throwError $ "non-array permission in a recursive perm body"
                               ++ " depends on an existential variable!"


----------------------------------------------------------------------
-- Translating IRT type variables
----------------------------------------------------------------------

data IRTVarIdxs = IRTVarIdxsNil
                | IRTVarIdxsCons Natural IRTVarIdxs
                | IRTVarIdxsAppend IRTVarIdxs IRTVarIdxs
                | IRTVarIdxsConcat [IRTVarIdxs]
                | IRTVarRec -- the recursive case
                deriving Show

pattern IRTVarIdx ix =  IRTVarIdxsCons ix IRTVarIdxsNil

-- | Translate a recursive permission's body to a SAW core list of its IRT
-- type variables given the name of the recursive permission being defined
-- and its argument context
translateCompleteIRTTyVars :: SharedContext -> PermEnv ->
                              NamedPermName ns args tp -> CruCtx args ->
                              Mb args (ValuePerm a) ->
                              IO (TypedTerm, IRTVarIdxs)
translateCompleteIRTTyVars sc env npn_rec args p =
  do let m = runIRTTyVarsTransM npn_rec args (valuePermIRTTyVars p)
         failOrListSortOpenTerm = either (OpenTerm . fail)
                                         (listSortOpenTerm . fst)
     tm <- completeOpenTermTyped sc $
           runNilTypeTransM (lambdaExprCtx args $
                              failOrListSortOpenTerm <$> m) env
     let errInfo = RL.map (\_ -> error "!!!") (cruCtxProxies args)
         err_or_ixs = runTransM m (TypeTransInfo errInfo env)
     case err_or_ixs of
       Left str -> fail str
       Right (_, ixs) -> return (tm, ixs)

-- | ...
-- ... Like 'transTupleTerm', but returns the empty list if 'transTerms' is
-- empty and a singleton list containing the result of 'transTupleTerm'
-- otherwise. This is used to avoid adding unnecessary @unit@s to the list of
-- type variables when translating IRTs.
irtTTranslateVar :: (IsTermTrans tr, Translate TypeTransInfo args a tr,
                     Substable PartialSubst a Maybe, NuMatching a) =>
                    Mb (args :++: ext) a ->
                    IRTTyVarsTransM args ext ([OpenTerm], IRTVarIdxs)
irtTTranslateVar p =
  do p' <- irtTSubstExt p
     p_trans <- liftIRTTyVarsTransM (translate p')
     case transTerms p_trans of
       [] -> return ([], IRTVarIdxsNil)
       _  -> do ix <- irtTNextIndex
                return ([transTupleTerm p_trans], IRTVarIdx ix)

-- | ...
irtTTranslateSigmaType :: TypeRepr tp ->
                          IRTTyVarsTransM args ext OpenTerm
irtTTranslateSigmaType tp =
  typeTransTupleType <$> liftIRTTyVarsTransM (translateClosed tp)

-- | Get all IRT type variables in a value perm
valuePermIRTTyVars :: Mb (args :++: ext) (ValuePerm a) ->
                      IRTTyVarsTransM args ext ([OpenTerm], IRTVarIdxs)
valuePermIRTTyVars [nuP| ValPerm_Eq _ |] = return ([], IRTVarIdxsNil)
valuePermIRTTyVars [nuP| ValPerm_Or p1 p2 |] =
  do (tps1, ixs1) <- valuePermIRTTyVars p1
     (tps2, ixs2) <- valuePermIRTTyVars p2
     return (tps1 ++ tps2, IRTVarIdxsAppend ixs1 ixs2)
valuePermIRTTyVars [nuP| ValPerm_Exists p |] =
  do let tp = mbBindingType p
     tp_trans <- irtTTranslateSigmaType tp
     ix <- irtTNextIndex
     pCbn <- irtTMbCombine p
     (tps, ixs) <- inExtIRTTyVarsTransM (valuePermIRTTyVars pCbn)
     return (tp_trans : tps, IRTVarIdxsCons ix ixs)
valuePermIRTTyVars p@[nuP| ValPerm_Named npn args off |] =
  namedPermIRTTyVars p npn args off
valuePermIRTTyVars p@[nuP| ValPerm_Var _ _ |] =
  irtTTranslateVar p
valuePermIRTTyVars [nuP| ValPerm_Conj ps |] =
  do (tps, ixs) <- unzip <$> mapM atomicPermIRTTyVars (mbList ps)
     return (concat tps, IRTVarIdxsConcat ixs)

-- | Get all IRT type variables in a named permission application. The first
-- argument must be either 'ValPerm_Named' or 'Perm_NamedConj' applied to the
-- remaining arguments.
namedPermIRTTyVars :: (Translate TypeTransInfo args a (TypeTrans tr),
                       Substable PartialSubst a Maybe, NuMatching a) =>
                      Mb (args :++: ext) a ->
                      Mb (args :++: ext) (NamedPermName ns args' tp) ->
                      Mb (args :++: ext) (PermExprs args') ->
                      Mb (args :++: ext) (PermOffset tp) ->
                      IRTTyVarsTransM args ext ([OpenTerm], IRTVarIdxs)
namedPermIRTTyVars p npn args off =
  do IRTTyVarsTransCtx npn_rec argsCtx extCtx <- ask
     case testNamedPermNameEq npn_rec <$> npn of
       [nuP| Just (Refl, Refl, Refl) |] ->
         if mbCombine (nus argsCtx (mbPure extCtx . namesToExprs)) == args &&
            mbCombine (mbPure argsCtx (mbPure extCtx NoPermOffset)) == off
         then return ([], IRTVarRec)
         else throwError $ "recursive permission applied to different"
                           ++ " arguments in its definition!"
       _ -> do p' <- irtTSubstExt p
               p_trans <- liftIRTTyVarsTransM (translate p')
               ix <- irtTNextIndex
               return ([typeTransTupleType p_trans], IRTVarIdx ix)

-- | Get all IRT type variables in an atomic perm
atomicPermIRTTyVars :: Mb (args :++: ext) (AtomicPerm a) ->
                       IRTTyVarsTransM args ext ([OpenTerm], IRTVarIdxs)
atomicPermIRTTyVars [nuP| Perm_LLVMField fld |] =
  valuePermIRTTyVars (fmap llvmFieldContents fld)
atomicPermIRTTyVars [nuP| Perm_LLVMArray mb_ap |] =
  do let mb_flds = fmap llvmArrayFields mb_ap
         flds = fmap (fmap llvmArrayFieldToAtomicPerm) (mbList mb_flds)
     (fld_tps, ixs) <- unzip <$> mapM atomicPermIRTTyVars flds
     return (concat fld_tps, IRTVarIdxsConcat ixs)
atomicPermIRTTyVars [nuP| Perm_LLVMBlock bp |] =
  shapeExprIRTTyVars (fmap llvmBlockShape bp)
atomicPermIRTTyVars [nuP| Perm_LLVMFree _ |] = return ([], IRTVarIdxsNil)
atomicPermIRTTyVars [nuP| Perm_LLVMFunPtr _ p |] =
  valuePermIRTTyVars p
atomicPermIRTTyVars [nuP| Perm_IsLLVMPtr |] = return ([], IRTVarIdxsNil)
atomicPermIRTTyVars [nuP| Perm_LLVMBlockShape sh |] =
  shapeExprIRTTyVars sh
atomicPermIRTTyVars p@[nuP| Perm_NamedConj npn args off |] =
  namedPermIRTTyVars p npn args off
atomicPermIRTTyVars [nuP| Perm_LLVMFrame _ |] = return ([], IRTVarIdxsNil)
atomicPermIRTTyVars [nuP| Perm_LOwned _ _ |] =
  error "lowned permission in an IRT definition!"
atomicPermIRTTyVars [nuP| Perm_LCurrent _ |] = return ([], IRTVarIdxsNil)
atomicPermIRTTyVars [nuP| Perm_Struct ps |] = valuePermsIRTTyVars ps
atomicPermIRTTyVars [nuP| Perm_Fun fun_perm |] =
  error "fun perm in an IRT definition!"
-- TODO What do I do with this case? It's not included in 'translate'...
atomicPermIRTTyVars [nuP| Perm_BVProp prop |] = return ([], IRTVarIdxsNil)

-- | Get all IRT type variables in a shape expression
shapeExprIRTTyVars :: Mb (args :++: ext) (PermExpr (LLVMShapeType w)) ->
                      IRTTyVarsTransM args ext ([OpenTerm], IRTVarIdxs)
shapeExprIRTTyVars p@[nuP| PExpr_Var _ |] =
  irtTTranslateVar p
shapeExprIRTTyVars [nuP| PExpr_EmptyShape |] = return ([], IRTVarIdxsNil)
shapeExprIRTTyVars [nuP| PExpr_EqShape _ |] = return ([], IRTVarIdxsNil)
shapeExprIRTTyVars [nuP| PExpr_PtrShape _ _ sh |] =
  shapeExprIRTTyVars sh
shapeExprIRTTyVars [nuP| PExpr_FieldShape fsh |] =
  fieldShapeIRTTyVars fsh
shapeExprIRTTyVars [nuP| PExpr_ArrayShape _ _ fshs |] = 
  do (tps, ixs) <- unzip <$> mapM fieldShapeIRTTyVars (mbList fshs)
     return (concat tps, IRTVarIdxsConcat ixs)
shapeExprIRTTyVars [nuP| PExpr_SeqShape sh1 sh2 |] =
  do (tps1, ixs1) <- shapeExprIRTTyVars sh1
     (tps2, ixs2) <- shapeExprIRTTyVars sh2
     return (tps1 ++ tps2, IRTVarIdxsAppend ixs1 ixs2)
shapeExprIRTTyVars [nuP| PExpr_OrShape sh1 sh2 |] =
  do (tps1, ixs1) <- shapeExprIRTTyVars sh1
     (tps2, ixs2) <- shapeExprIRTTyVars sh2
     return (tps1 ++ tps2, IRTVarIdxsAppend ixs1 ixs2)
shapeExprIRTTyVars [nuP| PExpr_ExShape mb_sh |] =
  do let tp = mbBindingType mb_sh
     tp_trans <- irtTTranslateSigmaType tp
     ix <- irtTNextIndex
     shCbn <- irtTMbCombine mb_sh
     (tps, ixs) <- inExtIRTTyVarsTransM (shapeExprIRTTyVars shCbn)
     return (tp_trans : tps, IRTVarIdxsCons ix ixs)

-- | Get all IRT type variables in a field shape
fieldShapeIRTTyVars :: Mb (args :++: ext) (LLVMFieldShape w) ->
                       IRTTyVarsTransM args ext ([OpenTerm], IRTVarIdxs)
fieldShapeIRTTyVars [nuP| LLVMFieldShape p |] = valuePermIRTTyVars p

-- | Get all IRT type variables in a set of value perms
valuePermsIRTTyVars :: Mb (args :++: ext) (ValuePerms ps) ->
                       IRTTyVarsTransM args ext ([OpenTerm], IRTVarIdxs)
valuePermsIRTTyVars [nuP| ValPerms_Nil |] = return ([], IRTVarIdxsNil)
valuePermsIRTTyVars [nuP| ValPerms_Cons ps p |] =
  do (tps1, ixs1) <- valuePermsIRTTyVars ps
     (tps2, ixs2) <- valuePermIRTTyVars p
     return (tps1 ++ tps2, IRTVarIdxsAppend ixs1 ixs2)


----------------------------------------------------------------------
-- The IRTDesc translation monad
----------------------------------------------------------------------

-- | Contextual info for translating IRT type descriptions
data IRTDescTransInfo ctx =
  IRTDescTransInfo { irtDExprCtx :: ExprTransCtx ctx,
                     irtDPermEnv :: PermEnv,
                     irtDTyVars  :: OpenTerm
                   }

-- | Build an empty 'IRTDescTransInfo' from a 'PermEnv' and type var 'Ident'
emptyIRTDescTransInfo :: PermEnv -> Ident -> IRTDescTransInfo RNil
emptyIRTDescTransInfo env tyVarsIdent =
  IRTDescTransInfo MNil env (globalOpenTerm tyVarsIdent)

-- | ...
irtDInArgsCtx :: IRTDescTransM args OpenTerm -> IRTDescTransM args OpenTerm
irtDInArgsCtx m =
  do args <- exprCtxToTerms <$> infoCtx <$> ask
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


----------------------------------------------------------------------
-- Translating IRT type descriptions
----------------------------------------------------------------------

-- | ...
translateCompleteIRTDesc :: SharedContext -> PermEnv -> 
                            Ident -> CruCtx args ->
                            Mb args (ValuePerm a) -> IRTVarIdxs ->
                            IO TypedTerm
translateCompleteIRTDesc sc env tyVarsIdent args p ixs =
  do tm <- completeOpenTerm sc $
           runTransM (lambdaExprCtx args . irtDInArgsCtx $
                        do in_mu <- valuePermIRTDesc p ixs
                           irtCtorOpenTerm "Prelude.IRT_mu" [in_mu])
                     (emptyIRTDescTransInfo env tyVarsIdent)
     let irtDescOpenTerm ectx = return $
           dataTypeOpenTerm "Prelude.IRTDesc"
             [ applyOpenTermMulti (globalOpenTerm tyVarsIdent)
                                  (exprCtxToTerms ectx) ]
     tp <- completeOpenTerm sc $
           runNilTypeTransM (translateClosed args >>= \tptrans ->
                              piTransM "e" tptrans irtDescOpenTerm) env
     return $ TypedTerm tm tp

irtCtorOpenTerm :: Ident -> [OpenTerm] -> IRTDescTransM ctx OpenTerm
irtCtorOpenTerm c all_args =
  do tyVarsTm <- irtDTyVars <$> ask
     return $ ctorOpenTerm c (tyVarsTm : all_args)

irtUnitOpenTerm :: IRTDescTransM ctx OpenTerm
irtUnitOpenTerm = irtCtorOpenTerm "Prelude.IRT_unit" []

irtVarTOpenTerm :: IRTVarIdxs -> IRTDescTransM ctx OpenTerm
irtVarTOpenTerm IRTVarIdxsNil = irtUnitOpenTerm
irtVarTOpenTerm (IRTVarIdx ix) = irtCtorOpenTerm "Prelude.IRT_varT" [natOpenTerm ix]
irtVarTOpenTerm _ = error "malformed IRTVarIdxs"

-- TODO Fix the two functions below

-- | Like 'tupleOfTypes' but with @IRT_prod@
irtProdOfTypes :: [OpenTerm] -> IRTDescTransM ctx OpenTerm
irtProdOfTypes [x] = return x
irtProdOfTypes xs = irtProdOpenTerm xs

-- | Like 'tupleTypeOpenTerm' but with @IRT_prod@
irtProdOpenTerm :: [OpenTerm] -> IRTDescTransM ctx OpenTerm
irtProdOpenTerm [] = irtUnitOpenTerm
irtProdOpenTerm (x:xs) =
  do xs' <- irtProdOpenTerm xs
     irtCtorOpenTerm "Prelude.IRT_prod" [x, xs']

valuePermIRTDesc :: Mb ctx (ValuePerm a) -> IRTVarIdxs ->
                    IRTDescTransM ctx OpenTerm
valuePermIRTDesc [nuP| ValPerm_Eq _ |] _ = irtUnitOpenTerm
valuePermIRTDesc [nuP| ValPerm_Or p1 p2 |] (IRTVarIdxsAppend ixs1 ixs2) =
  do x1 <- valuePermIRTDesc p1 ixs1
     x2 <- valuePermIRTDesc p2 ixs2
     irtCtorOpenTerm "Prelude.IRT_Either" [x1, x2]
valuePermIRTDesc [nuP| ValPerm_Exists p |] (IRTVarIdxsCons ix ixs) =
  do let tp = mbBindingType p
     tp_trans <- tupleTypeTrans <$> translateClosed tp
     xf <- lambdaTransM "x_irt" tp_trans (\x ->
             inExtTransM x $ valuePermIRTDesc (mbCombine p) ixs)
     irtCtorOpenTerm "Prelude.IRT_sigT" [natOpenTerm ix, xf]
valuePermIRTDesc [nuP| ValPerm_Named _ _ _ |] IRTVarRec =
  irtCtorOpenTerm "Prelude.IRT_varD" [natOpenTerm 0]
valuePermIRTDesc [nuP| ValPerm_Named _ _ _ |] ix =
  irtVarTOpenTerm ix
valuePermIRTDesc [nuP| ValPerm_Var _ _ |] ix =
  irtVarTOpenTerm ix
valuePermIRTDesc [nuP| ValPerm_Conj ps |] (IRTVarIdxsConcat ixss) =
  do xs <- zipWithM atomicPermIRTDesc (mbList ps) ixss
     irtProdOfTypes xs

atomicPermIRTDesc :: Mb ctx (AtomicPerm a) -> IRTVarIdxs ->
                     IRTDescTransM ctx OpenTerm
atomicPermIRTDesc [nuP| Perm_LLVMField fld |] ixs =
  valuePermIRTDesc (fmap llvmFieldContents fld) ixs
atomicPermIRTDesc [nuP| Perm_LLVMArray mb_ap |] (IRTVarIdxsConcat ixss) =
  do let w = natVal2 mb_ap
         w_term = natOpenTerm w
         mb_len = fmap llvmArrayLen mb_ap
         mb_flds = fmap llvmArrayFields mb_ap
         flds = fmap (fmap llvmArrayFieldToAtomicPerm) (mbList mb_flds)
     len_term <- translate1 mb_len
     xs <- zipWithM atomicPermIRTDesc flds ixss
     xs_term <- irtProdOfTypes xs
     irtCtorOpenTerm "Prelude.IRT_BVVec" [w_term, len_term, xs_term]
atomicPermIRTDesc [nuP| Perm_LLVMBlock bp |] ixs =
  shapeExprIRTDesc (fmap llvmBlockShape bp) ixs
atomicPermIRTDesc [nuP| Perm_LLVMFree _ |] _ = irtUnitOpenTerm
atomicPermIRTDesc [nuP| Perm_LLVMFunPtr _ p |] ixs =
  valuePermIRTDesc p ixs
atomicPermIRTDesc [nuP| Perm_IsLLVMPtr |] _ = irtUnitOpenTerm
atomicPermIRTDesc [nuP| Perm_LLVMBlockShape sh |] ixs =
  shapeExprIRTDesc sh ixs
atomicPermIRTDesc [nuP| Perm_NamedConj _ _ _ |] IRTVarRec =
  irtCtorOpenTerm "Prelude.IRT_varD" [natOpenTerm 0]
atomicPermIRTDesc [nuP| Perm_NamedConj _ _ _ |] ix =
  irtVarTOpenTerm ix
atomicPermIRTDesc [nuP| Perm_LLVMFrame _ |] _ = irtUnitOpenTerm
atomicPermIRTDesc [nuP| Perm_LOwned _ _ |] _ =
  error "lowned permission in an IRT definition!"
atomicPermIRTDesc [nuP| Perm_LCurrent _ |] _ = irtUnitOpenTerm
atomicPermIRTDesc [nuP| Perm_Struct ps |] ixs = valuePermsIRTDesc ps ixs
atomicPermIRTDesc [nuP| Perm_Fun fun_perm |] _ =
  error "fun perm in an IRT definition!"
atomicPermIRTDesc [nuP| Perm_BVProp prop |] _ = irtUnitOpenTerm

shapeExprIRTDesc :: Mb ctx (PermExpr (LLVMShapeType w)) -> IRTVarIdxs ->
                    IRTDescTransM ctx OpenTerm
shapeExprIRTDesc [nuP| PExpr_EmptyShape |] _ = irtUnitOpenTerm
shapeExprIRTDesc [nuP| PExpr_EqShape _ |] _ = irtUnitOpenTerm
shapeExprIRTDesc [nuP| PExpr_PtrShape _ _ sh |] ixs =
  shapeExprIRTDesc sh ixs
shapeExprIRTDesc [nuP| PExpr_FieldShape fsh |] ixs =
  fieldShapeIRTDesc fsh ixs
shapeExprIRTDesc [nuP| PExpr_ArrayShape mb_len _ mb_fshs |] (IRTVarIdxsConcat ixss) =
  do let w = natVal4 mb_len
     let w_term = natOpenTerm w
     len_term <- translate1 mb_len
     xs <- zipWithM fieldShapeIRTDesc (mbList mb_fshs) ixss
     xs_term <- irtProdOfTypes xs
     irtCtorOpenTerm "Prelude.IRT_BVVec" [w_term, len_term, xs_term]
shapeExprIRTDesc [nuP| PExpr_SeqShape sh1 sh2 |] (IRTVarIdxsAppend ixs1 ixs2) =
  do x1 <- shapeExprIRTDesc sh1 ixs1
     x2 <- shapeExprIRTDesc sh2 ixs2
     irtCtorOpenTerm "Prelude.IRT_prod" [x1, x2]
shapeExprIRTDesc [nuP| PExpr_OrShape sh1 sh2 |] (IRTVarIdxsAppend ixs1 ixs2) =
  do x1 <- shapeExprIRTDesc sh1 ixs1
     x2 <- shapeExprIRTDesc sh2 ixs2
     irtCtorOpenTerm "Prelude.IRT_Either" [x1, x2]
shapeExprIRTDesc [nuP| PExpr_ExShape mb_sh |] (IRTVarIdxsCons ix ixs) =
  do let tp = mbBindingType mb_sh
     tp_trans <- tupleTypeTrans <$> translateClosed tp
     xf <- lambdaTransM "x_irt" tp_trans (\x ->
             inExtTransM x $ shapeExprIRTDesc (mbCombine mb_sh) ixs)
     irtCtorOpenTerm "Prelude.IRT_sigT" [natOpenTerm ix, xf]

fieldShapeIRTDesc :: Mb ctx (LLVMFieldShape w) -> IRTVarIdxs ->
                     IRTDescTransM ctx OpenTerm
fieldShapeIRTDesc [nuP| LLVMFieldShape p |] ixs = valuePermIRTDesc p ixs

-- TODO Fix this
valuePermsIRTDesc :: Mb ctx (ValuePerms ps) -> IRTVarIdxs ->
                     IRTDescTransM ctx OpenTerm
valuePermsIRTDesc [nuP| ValPerms_Nil |] _ = irtUnitOpenTerm
valuePermsIRTDesc [nuP| ValPerms_Cons ps p |] (IRTVarIdxsAppend ixs1 ixs2) =
  do xs <- valuePermsIRTDesc ps ixs1
     x  <- valuePermIRTDesc p ixs2
     irtCtorOpenTerm "Prelude.IRT_prod" [xs, x]
