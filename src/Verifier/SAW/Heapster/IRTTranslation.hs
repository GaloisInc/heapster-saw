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
irtTMbCombine :: forall args ext ctx a.
                 Mb (args :++: ext) (Mb ctx a) ->
                 IRTTyVarsTransM args ext (Mb (args :++: (ext :++: ctx)) a)
irtTMbCombine x =
  do ext <- irtTExtCtx <$> ask
     return $ mbCombine (fmap mbCombine (mbSeparate @_ @args ext x))

-- | Create an @args :++: ext@ binding
irtNus :: (RAssign Name args -> RAssign Name ext -> b) ->
          IRTTyVarsTransM args ext (Mb (args :++: ext) b)
irtNus f = 
  do args <- irtTArgsCtx <$> ask
     ext  <- irtTExtCtx  <$> ask
     return $ mbCombine (nus args (nus ext . f))

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

-- | ...
setIRTVarIdxs :: IRTVarTreeShape -> IRTVarIdxs
setIRTVarIdxs tree = evalState (mapM (\_ -> nextIdx) tree) 0
  where nextIdx :: State Natural Natural
        nextIdx = state (\i -> (i,i+1))


----------------------------------------------------------------------
-- Translating IRT type variables
----------------------------------------------------------------------

-- | Translate a recursive permission's body to a SAW core list of its IRT
-- type variables given the name of the recursive permission being defined
-- and its argument context
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
valuePermIRTTyVars [nuP| ValPerm_Eq _ |] = return ([], IRTVarsNil)
valuePermIRTTyVars [nuP| ValPerm_Or p1 p2 |] =
  do (tps1, ixs1) <- valuePermIRTTyVars p1
     (tps2, ixs2) <- valuePermIRTTyVars p2
     return (tps1 ++ tps2, IRTVarsAppend ixs1 ixs2)
valuePermIRTTyVars [nuP| ValPerm_Exists p |] =
  do let tp = mbBindingType p
         tp_trans = typeTransTupleType <$> translateClosed tp
     pCbn <- irtTMbCombine p
     (tps, ixs) <- inExtIRTTyVarsTransM (valuePermIRTTyVars pCbn)
     return (tp_trans : tps, IRTVarsCons () ixs)
valuePermIRTTyVars p@[nuP| ValPerm_Named npn args off |] =
  namedPermIRTTyVars p npn args off
valuePermIRTTyVars p@[nuP| ValPerm_Var x _ |] =
  irtTTranslateVar p x
valuePermIRTTyVars [nuP| ValPerm_Conj ps |] =
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
     case testNamedPermNameEq npn_rec <$> npn of
       [nuP| Just (Refl, Refl, Refl) |] ->
         if npn_args == args && npn_off == off
         then return ([], IRTRecVar)
         else throwError $ "recursive permission applied to different"
                           ++ " arguments in its definition!"
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
                              (mbSwap (mbSeparate extCtx x))
         tp_trans = getConst $ RL.get memb argsCtx
     -- if x (and thus also p) has no translation, return an empty list
     case tp_trans of
       [] -> return ([], IRTVarsNil)
       _  -> return ([tupleOfTypes <$> tm_trans], IRTVar ())

-- | Get all IRT type variables in an atomic perm
atomicPermIRTTyVars :: Mb (args :++: ext) (AtomicPerm a) ->
                       IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                                 IRTVarTreeShape)
atomicPermIRTTyVars [nuP| Perm_LLVMField fld |] =
  valuePermIRTTyVars (fmap llvmFieldContents fld)
atomicPermIRTTyVars [nuP| Perm_LLVMArray mb_ap |] =
  do let mb_flds = fmap llvmArrayFields mb_ap
         flds = fmap (fmap llvmArrayFieldToAtomicPerm) (mbList mb_flds)
     (fld_tps, ixs) <- unzip <$> mapM atomicPermIRTTyVars flds
     return (concat fld_tps, IRTVarsConcat ixs)
atomicPermIRTTyVars [nuP| Perm_LLVMBlock bp |] =
  shapeExprIRTTyVars (fmap llvmBlockShape bp)
atomicPermIRTTyVars [nuP| Perm_LLVMFree _ |] = return ([], IRTVarsNil)
atomicPermIRTTyVars [nuP| Perm_LLVMFunPtr _ p |] =
  valuePermIRTTyVars p
atomicPermIRTTyVars [nuP| Perm_IsLLVMPtr |] = return ([], IRTVarsNil)
atomicPermIRTTyVars [nuP| Perm_LLVMBlockShape sh |] =
  shapeExprIRTTyVars sh
atomicPermIRTTyVars p@[nuP| Perm_NamedConj npn args off |] =
  namedPermIRTTyVars p npn args off
atomicPermIRTTyVars [nuP| Perm_LLVMFrame _ |] = return ([], IRTVarsNil)
atomicPermIRTTyVars [nuP| Perm_LOwned _ _ |] =
  throwError "lowned permission in an IRT definition!"
atomicPermIRTTyVars [nuP| Perm_LCurrent _ |] = return ([], IRTVarsNil)
atomicPermIRTTyVars [nuP| Perm_Struct ps |] = valuePermsIRTTyVars ps
atomicPermIRTTyVars [nuP| Perm_Fun _ |] =
  throwError "fun perm in an IRT definition!"
atomicPermIRTTyVars [nuP| Perm_BVProp _ |] =
  throwError "BVProp in an IRT definition!"

-- | Get all IRT type variables in a shape expression
shapeExprIRTTyVars :: Mb (args :++: ext) (PermExpr (LLVMShapeType w)) ->
                      IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                                IRTVarTreeShape)
shapeExprIRTTyVars p@[nuP| PExpr_Var x |] =
  irtTTranslateVar p x
shapeExprIRTTyVars [nuP| PExpr_EmptyShape |] = return ([], IRTVarsNil)
shapeExprIRTTyVars [nuP| PExpr_EqShape _ |] = return ([], IRTVarsNil)
shapeExprIRTTyVars [nuP| PExpr_PtrShape _ _ sh |] =
  shapeExprIRTTyVars sh
shapeExprIRTTyVars [nuP| PExpr_FieldShape fsh |] =
  fieldShapeIRTTyVars fsh
shapeExprIRTTyVars [nuP| PExpr_ArrayShape _ _ fshs |] = 
  do (tps, ixs) <- unzip <$> mapM fieldShapeIRTTyVars (mbList fshs)
     return (concat tps, IRTVarsConcat ixs)
shapeExprIRTTyVars [nuP| PExpr_SeqShape sh1 sh2 |] =
  do (tps1, ixs1) <- shapeExprIRTTyVars sh1
     (tps2, ixs2) <- shapeExprIRTTyVars sh2
     return (tps1 ++ tps2, IRTVarsAppend ixs1 ixs2)
shapeExprIRTTyVars [nuP| PExpr_OrShape sh1 sh2 |] =
  do (tps1, ixs1) <- shapeExprIRTTyVars sh1
     (tps2, ixs2) <- shapeExprIRTTyVars sh2
     return (tps1 ++ tps2, IRTVarsAppend ixs1 ixs2)
shapeExprIRTTyVars [nuP| PExpr_ExShape mb_sh |] =
  do let tp = mbBindingType mb_sh
         tp_trans = typeTransTupleType <$> translateClosed tp
     shCbn <- irtTMbCombine mb_sh
     (tps, ixs) <- inExtIRTTyVarsTransM (shapeExprIRTTyVars shCbn)
     return (tp_trans : tps, IRTVarsCons () ixs)

-- | Get all IRT type variables in a field shape
fieldShapeIRTTyVars :: Mb (args :++: ext) (LLVMFieldShape w) ->
                       IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                                 IRTVarTreeShape)
fieldShapeIRTTyVars [nuP| LLVMFieldShape p |] = valuePermIRTTyVars p

-- | Get all IRT type variables in a set of value perms
valuePermsIRTTyVars :: Mb (args :++: ext) (ValuePerms ps) ->
                       IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                                 IRTVarTreeShape)
valuePermsIRTTyVars [nuP| ValPerms_Nil |] = return ([], IRTVarsNil)
valuePermsIRTTyVars [nuP| ValPerms_Cons ps p |] =
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

-- | Build an empty 'IRTDescTransInfo' from a 'PermEnv' and type var 'Ident'
emptyIRTDescTransInfo :: PermEnv -> Ident -> IRTDescTransInfo RNil
emptyIRTDescTransInfo env tyVarsIdent =
  IRTDescTransInfo MNil env (globalOpenTerm tyVarsIdent)

-- | ...
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

-- | ...
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

-- | ...
irtCtor :: Ident -> [OpenTerm] -> IRTDescTransM ctx [OpenTerm]
irtCtor c all_args =
  do tm <- irtCtorOpenTerm c all_args
     return [tm]


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
                        do in_mu <- valuePermIRTDesc p ixs >>= irtProd
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

valuePermIRTDesc :: Mb ctx (ValuePerm a) -> IRTVarIdxs ->
                    IRTDescTransM ctx [OpenTerm]
valuePermIRTDesc [nuP| ValPerm_Eq _ |] _ = return []
valuePermIRTDesc [nuP| ValPerm_Or p1 p2 |] (IRTVarsAppend ixs1 ixs2) =
  do x1 <- valuePermIRTDesc p1 ixs1 >>= irtProd
     x2 <- valuePermIRTDesc p2 ixs2 >>= irtProd
     irtCtor "Prelude.IRT_Either" [x1, x2]
valuePermIRTDesc [nuP| ValPerm_Exists p |] (IRTVarsCons ix ixs) =
  do let tp = mbBindingType p
     tp_trans <- tupleTypeTrans <$> translateClosed tp
     xf <- lambdaTransM "x_irt" tp_trans (\x -> inExtTransM x $
             valuePermIRTDesc (mbCombine p) ixs >>= irtProd)
     irtCtor "Prelude.IRT_sigT" [natOpenTerm ix, xf]
valuePermIRTDesc [nuP| ValPerm_Named _ _ _ |] IRTRecVar =
  irtCtor "Prelude.IRT_varD" [natOpenTerm 0]
valuePermIRTDesc [nuP| ValPerm_Named _ _ _ |] ix = irtVarT ix
valuePermIRTDesc [nuP| ValPerm_Var _ _ |] ix = irtVarT ix
valuePermIRTDesc [nuP| ValPerm_Conj ps |] (IRTVarsConcat ixss) =
  concat <$> zipWithM atomicPermIRTDesc (mbList ps) ixss
valuePermIRTDesc _ ixs = error $ "malformed IRTVarIdxs: " ++ show ixs

irtVarT :: IRTVarIdxs -> IRTDescTransM ctx [OpenTerm]
irtVarT IRTVarsNil = return []
irtVarT (IRTVar ix) = irtCtor "Prelude.IRT_varT" [natOpenTerm ix]
irtVarT ixs = error $ "malformed IRTVarIdxs: " ++ show ixs

atomicPermIRTDesc :: Mb ctx (AtomicPerm a) -> IRTVarIdxs ->
                     IRTDescTransM ctx [OpenTerm]
atomicPermIRTDesc [nuP| Perm_LLVMField fld |] ixs =
  valuePermIRTDesc (fmap llvmFieldContents fld) ixs
atomicPermIRTDesc [nuP| Perm_LLVMArray mb_ap |] (IRTVarsConcat ixss) =
  do let w = natVal2 mb_ap
         w_term = natOpenTerm w
         mb_len = fmap llvmArrayLen mb_ap
         mb_flds = fmap llvmArrayFields mb_ap
         flds = fmap (fmap llvmArrayFieldToAtomicPerm) (mbList mb_flds)
     len_term <- translate1 mb_len
     xs <- concat <$> zipWithM atomicPermIRTDesc flds ixss
     xs_term <- irtProd xs
     irtCtor "Prelude.IRT_BVVec" [w_term, len_term, xs_term]
atomicPermIRTDesc [nuP| Perm_LLVMBlock bp |] ixs =
  shapeExprIRTDesc (fmap llvmBlockShape bp) ixs
atomicPermIRTDesc [nuP| Perm_LLVMFree _ |] _ = return []
atomicPermIRTDesc [nuP| Perm_LLVMFunPtr _ p |] ixs =
  valuePermIRTDesc p ixs
atomicPermIRTDesc [nuP| Perm_IsLLVMPtr |] _ = return []
atomicPermIRTDesc [nuP| Perm_LLVMBlockShape sh |] ixs =
  shapeExprIRTDesc sh ixs
atomicPermIRTDesc [nuP| Perm_NamedConj _ _ _ |] IRTRecVar =
  irtCtor "Prelude.IRT_varD" [natOpenTerm 0]
atomicPermIRTDesc [nuP| Perm_NamedConj _ _ _ |] ix = irtVarT ix
atomicPermIRTDesc [nuP| Perm_LLVMFrame _ |] _ = return []
atomicPermIRTDesc [nuP| Perm_LOwned _ _ |] _ =
  error "lowned permission made it to IRTDesc translation"
atomicPermIRTDesc [nuP| Perm_LCurrent _ |] _ = return []
atomicPermIRTDesc [nuP| Perm_Struct ps |] ixs =
  valuePermsIRTDesc ps ixs
atomicPermIRTDesc [nuP| Perm_Fun _ |] _ =
  error "fun perm made it to IRTDesc translation"
atomicPermIRTDesc [nuP| Perm_BVProp _ |] _ =
  error "BVProp made it to IRTDesc translation"
atomicPermIRTDesc _ ixs = error $ "malformed IRTVarIdxs: " ++ show ixs

shapeExprIRTDesc :: Mb ctx (PermExpr (LLVMShapeType w)) -> IRTVarIdxs ->
                    IRTDescTransM ctx [OpenTerm]
shapeExprIRTDesc [nuP| PExpr_EmptyShape |] _ = return []
shapeExprIRTDesc [nuP| PExpr_EqShape _ |] _ = return []
shapeExprIRTDesc [nuP| PExpr_PtrShape _ _ sh |] ixs =
  shapeExprIRTDesc sh ixs
shapeExprIRTDesc [nuP| PExpr_FieldShape fsh |] ixs =
  fieldShapeIRTDesc fsh ixs
shapeExprIRTDesc [nuP| PExpr_ArrayShape mb_len _ mb_fshs |] (IRTVarsConcat ixss) =
  do let w = natVal4 mb_len
     let w_term = natOpenTerm w
     len_term <- translate1 mb_len
     xs <- concat <$> zipWithM fieldShapeIRTDesc (mbList mb_fshs) ixss
     xs_term <- irtProd xs
     irtCtor "Prelude.IRT_BVVec" [w_term, len_term, xs_term]
shapeExprIRTDesc [nuP| PExpr_SeqShape sh1 sh2 |] (IRTVarsAppend ixs1 ixs2) =
  do x1 <- shapeExprIRTDesc sh1 ixs1 >>= irtProd
     x2 <- shapeExprIRTDesc sh2 ixs2 >>= irtProd
     irtCtor "Prelude.IRT_prod" [x1, x2]
shapeExprIRTDesc [nuP| PExpr_OrShape sh1 sh2 |] (IRTVarsAppend ixs1 ixs2) =
  do x1 <- shapeExprIRTDesc sh1 ixs1 >>= irtProd
     x2 <- shapeExprIRTDesc sh2 ixs2 >>= irtProd
     irtCtor "Prelude.IRT_Either" [x1, x2]
shapeExprIRTDesc [nuP| PExpr_ExShape mb_sh |] (IRTVarsCons ix ixs) =
  do let tp = mbBindingType mb_sh
     tp_trans <- tupleTypeTrans <$> translateClosed tp
     xf <- lambdaTransM "x_irt" tp_trans (\x -> inExtTransM x $
             shapeExprIRTDesc (mbCombine mb_sh) ixs >>= irtProd)
     irtCtor "Prelude.IRT_sigT" [natOpenTerm ix, xf]
shapeExprIRTDesc _ ixs = error $ "malformed IRTVarIdxs: " ++ show ixs

fieldShapeIRTDesc :: Mb ctx (LLVMFieldShape w) -> IRTVarIdxs ->
                     IRTDescTransM ctx [OpenTerm]
fieldShapeIRTDesc [nuP| LLVMFieldShape p |] ixs = valuePermIRTDesc p ixs

valuePermsIRTDesc :: Mb ctx (ValuePerms ps) -> IRTVarIdxs ->
                     IRTDescTransM ctx [OpenTerm]
valuePermsIRTDesc [nuP| ValPerms_Nil |] _ = return []
valuePermsIRTDesc [nuP| ValPerms_Cons ps p |] (IRTVarsAppend ixs1 ixs2) =
  do xs <- valuePermsIRTDesc ps ixs1
     x  <- valuePermIRTDesc p ixs2
     return $ xs ++ x
valuePermsIRTDesc _ ixs = error $ "malformed IRTVarIdxs: " ++ show ixs


----------------------------------------------------------------------
-- Translating IRT definitions
----------------------------------------------------------------------

-- | ...
translateCompleteIRTDef :: SharedContext -> PermEnv -> 
                           Ident -> Ident -> CruCtx args ->
                           IO TypedTerm
translateCompleteIRTDef sc env tyVarsIdent descIdent args =
  completeOpenTermTyped sc $
  runNilTypeTransM (lambdaExprCtx args $
                     irtDefinition tyVarsIdent descIdent) env

-- | ...
translateCompleteIRTFoldFun :: SharedContext -> PermEnv -> 
                               Ident -> Ident -> Ident -> CruCtx args ->
                               IO Term
translateCompleteIRTFoldFun sc env tyVarsIdent descIdent _ args =
  completeOpenTerm sc $
  runNilTypeTransM (lambdaExprCtx args $
                     irtFoldFun tyVarsIdent descIdent) env

-- | ...
translateCompleteIRTUnfoldFun :: SharedContext -> PermEnv -> 
                                 Ident -> Ident -> Ident -> CruCtx args ->
                                 IO Term
translateCompleteIRTUnfoldFun sc env tyVarsIdent descIdent _ args =
  completeOpenTerm sc $
  runNilTypeTransM (lambdaExprCtx args $
                     irtUnfoldFun tyVarsIdent descIdent) env

-- | ...
irtDefArgs :: Ident -> Ident -> TypeTransM args (OpenTerm, OpenTerm, OpenTerm)
irtDefArgs tyVarsIdent descIdent = 
  do args <- askExprCtxTerms
     let tyVars = applyOpenTermMulti (globalOpenTerm tyVarsIdent) args
         substs = ctorOpenTerm "Prelude.IRTs_Nil" [tyVars]
         desc   = applyOpenTermMulti (globalOpenTerm descIdent) args
     return (tyVars, substs, desc)

-- | ...
irtDefinition :: Ident -> Ident -> TypeTransM args OpenTerm
irtDefinition tyVarsIdent descIdent = 
  do (tyVars, substs, desc) <- irtDefArgs tyVarsIdent descIdent
     return $ dataTypeOpenTerm "Prelude.IRT" [tyVars, substs, desc]

-- | ...
irtFoldFun :: Ident -> Ident -> TypeTransM args OpenTerm
irtFoldFun tyVarsIdent descIdent = 
  do (tyVars, substs, desc) <- irtDefArgs tyVarsIdent descIdent
     return $ applyOpenTermMulti (globalOpenTerm "Prelude.foldIRT")
                                 [tyVars, substs, desc]

-- | ...
irtUnfoldFun :: Ident -> Ident -> TypeTransM args OpenTerm
irtUnfoldFun tyVarsIdent descIdent = 
  do (tyVars, substs, desc) <- irtDefArgs tyVarsIdent descIdent
     return $ applyOpenTermMulti (globalOpenTerm "Prelude.unfoldIRT")
                                 [tyVars, substs, desc]
