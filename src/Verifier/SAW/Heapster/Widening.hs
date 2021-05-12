{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE BangPatterns #-}

module Verifier.SAW.Heapster.Widening where

import Data.Maybe
import Data.List
import Data.Functor.Constant
import Data.Functor.Product
import Control.Monad.State
-- import Control.Monad.Cont
import GHC.TypeLits
import Control.Lens hiding ((:>), Index, Empty, ix, op)

import Data.Parameterized.Some

import Prettyprinter

import Lang.Crucible.LLVM.MemModel
import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits
import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Lang.Crucible.Types


----------------------------------------------------------------------
-- * The Widening Monad
----------------------------------------------------------------------

-- | A sequence of permissions for some list of variables that extends @vars@
data ExtVarPerms vars
  = ExtVarPerms_Base (ValuePerms vars)
  | forall var. ExtVarPerms_Mb (TypeRepr var) (Binding var
                                               (ExtVarPerms (vars :> var)))

$(mkNuMatching [t| forall vars. ExtVarPerms vars |])

extVarPerms_MbMulti :: CruCtx ctx -> Mb ctx (ExtVarPerms (vars :++: ctx)) ->
                       ExtVarPerms vars
extVarPerms_MbMulti CruCtxNil mb_ewid = elimEmptyMb mb_ewid
extVarPerms_MbMulti (CruCtxCons ctx tp) mb_ewid =
  extVarPerms_MbMulti ctx $
  fmap (ExtVarPerms_Mb tp) $ mbSeparate (MNil :>: Proxy) mb_ewid

newtype ExtVarPermsFun vars =
  ExtVarPermsFun { applyExtVarPermsFun ::
                     RAssign Name vars -> ExtVarPerms vars }

-- | A map from free variables to their permissions and whether they have been
-- "visited" yet
type WidNameMap = NameMap (Product ValuePerm (Constant Bool))

-- | Modify the entry in a 'WidNameMap' associated with a particular free
-- variable, starting from the default entry of @('ValPerm_True','False')@ if
-- the variable has not been entered into the map yet
wnMapAlter :: (Product ValuePerm (Constant Bool) a ->
               Product ValuePerm (Constant Bool) a) -> ExprVar a ->
              WidNameMap -> WidNameMap
wnMapAlter f =
  NameMap.alter $ \case
  Just entry -> Just $ f entry
  Nothing -> Just $ f (Pair ValPerm_True (Constant False))

-- | Look up the permission for a name in a 'WidNameMap'
wnMapGetPerm :: Name a -> WidNameMap -> ValuePerm a
wnMapGetPerm n nmap | Just (Pair p _) <- NameMap.lookup n nmap = p
wnMapGetPerm _ _ = ValPerm_True

-- | Build an 'ExtVarPermsFun' from a widening name map
wnMapExtWidFun :: WidNameMap -> ExtVarPermsFun vars
wnMapExtWidFun wnmap =
  ExtVarPermsFun $ \ns -> ExtVarPerms_Base $ RL.map (flip wnMapGetPerm wnmap) ns

newtype PolyContT r m a =
  PolyContT { runPolyContT :: forall x. (forall y. a -> m (r y)) -> m (r x) }

instance Functor (PolyContT r m) where
  fmap f m = m >>= return . f

instance Applicative (PolyContT r m) where
  pure = return
  (<*>) = ap

instance Monad (PolyContT r m) where
  return x = PolyContT $ \k -> k x
  (PolyContT m) >>= f =
    PolyContT $ \k -> m $ \a -> runPolyContT (f a) k

data WidState = WidState { _wsNameMap :: WidNameMap,
                           _wsPPInfo :: PPInfo }

makeLenses ''WidState

type WideningM =
  StateT WidState (PolyContT ExtVarPermsFun Identity)

runWideningM :: WideningM () -> WidNameMap -> RAssign Name args ->
                ExtVarPerms args
runWideningM m wnmap =
  applyExtVarPermsFun $ runIdentity $
  runPolyContT (runStateT m $ WidState wnmap emptyPPInfo)
  (Identity . wnMapExtWidFun . _wsNameMap . snd)

openMb :: CruCtx ctx -> Mb ctx a -> WideningM (RAssign Name ctx, a)
openMb ctx mb_a =
  lift $ PolyContT $ \k -> Identity $ ExtVarPermsFun $ \ns ->
  extVarPerms_MbMulti ctx $
  mbMap2 (\ns' a ->
           applyExtVarPermsFun (runIdentity $ k (ns',a)) (RL.append ns ns'))
  (nuMulti (cruCtxProxies ctx) id) mb_a

bindFreshVar :: TypeRepr tp -> WideningM (ExprVar tp)
bindFreshVar tp =
  (snd <$> openMb (singletonCruCtx tp) (nu id)) >>= \n ->
  setVarNameM "var" n >>
  return n

visitM :: ExprVar a -> WideningM ()
visitM n = modify $ over wsNameMap $ wnMapAlter (\(Pair p _) ->
                                                  Pair p (Constant True)) n

isVisitedM :: ExprVar a -> WideningM Bool
isVisitedM n =
  maybe False (\(Pair _ (Constant b)) -> b) <$>
  NameMap.lookup n <$> view wsNameMap <$> get

getVarPermM :: ExprVar a -> WideningM (ValuePerm a)
getVarPermM n = wnMapGetPerm n <$> view wsNameMap <$> get

setVarPermM :: ExprVar a -> ValuePerm a -> WideningM ()
setVarPermM n p =
  modify $ over wsNameMap $ wnMapAlter (\(Pair _ isv) -> Pair p isv) n

-- | Set the permissions for @x &+ off@ to @p@, by setting the permissions for
-- @x@ to @p - off@
setOffVarPermM :: ExprVar a -> PermOffset a -> ValuePerm a -> WideningM ()
setOffVarPermM x off p =
  setVarPermM x (offsetPerm (negatePermOffset off) p)

setVarPermsM :: RAssign Name ctx -> RAssign ValuePerm ctx -> WideningM ()
setVarPermsM MNil MNil = return ()
setVarPermsM (ns :>: n) (ps :>: p) = setVarPermsM ns ps >> setVarPermM n p

setVarNameM :: String -> ExprVar tp -> WideningM ()
setVarNameM base x = modify $ over wsPPInfo $ ppInfoAddExprName base x

setVarNamesM :: String -> RAssign ExprVar tps -> WideningM ()
setVarNamesM base xs = modify $ over wsPPInfo $ ppInfoAddExprNames base xs

traceM :: (PPInfo -> Doc ()) -> WideningM ()
traceM f =
  (f <$> view wsPPInfo <$> get) >>= \doc ->
  tracePretty doc (return ())


----------------------------------------------------------------------
-- * Widening Itself
----------------------------------------------------------------------

{-
-- | Test if an expression in a binding is a free variable plus offset
mbAsOffsetVar :: KnownCruCtx vars -> Mb vars (PermExpr a) ->
                 Maybe (Name a, PermOffset a)
mbAsOffsetVar vars [nuP| PExpr_Var mb_x |]
  | Right n <- mbNameBoundP mb_x = Just (n, NoPermOffset)
mbAsOffsetVar vars [nuP| PExpr_LLVMOffset mb_x mb_off |]
  | Right n <- mbNameBoundP mb_x
  , Just off <- partialSubst (emptyPSubst vars) mb_off
  = Just (n, LLVMPermOffset off)
mbAsOffsetVar _ _ = Nothing
-}

-- | Take a permission @p1@ at some existing location and split it into some
-- @p1'*p1''@ such that @p1'@ will remain at the existing location and @p1''@
-- will be widened against @p1''@. Return @p1'@ and the result of widening
-- @p1''@ against @p2@.
splitWidenPerm :: TypeRepr a -> ValuePerm a -> ValuePerm a ->
                  WideningM (ValuePerm a, ValuePerm a)
splitWidenPerm tp p1 p2
  | permIsCopyable p1 = (p1,) <$> widenPerm tp p1 p2
splitWidenPerm _ p1 _ = return (p1, ValPerm_True)

-- | Take permissions @p1@ and @p2@ that are both on existing locations and
-- split them both into @p1'*p1''@ and @p2'*p2''@ such that @p1'@ and @p2'@
-- remain at the existing locations and @p1''@ and @p2''@ are widened against
-- each other. Return @p1'@, @p2'@, and the result of the further widening of
-- @p1''@ against @p2''@.
doubleSplitWidenPerm :: TypeRepr a -> ValuePerm a -> ValuePerm a ->
                        WideningM ((ValuePerm a, ValuePerm a), ValuePerm a)
doubleSplitWidenPerm tp p1 p2
  | permIsCopyable p1 && permIsCopyable p2
  = ((p1,p2),) <$> widenPerm tp p1 p2
doubleSplitWidenPerm _ p1 p2 =
  return ((p1, p2), ValPerm_True)


-- | Widen two expressions against each other
--
-- FIXME: document this more
widenExpr :: TypeRepr a -> PermExpr a -> PermExpr a -> WideningM (PermExpr a)
widenExpr tp e1 e2 =
  traceM (\i ->
           fillSep [pretty "widenExpr", permPretty i e1, permPretty i e2]) >>
  widenExpr' tp e1 e2

widenExpr' :: TypeRepr a -> PermExpr a -> PermExpr a -> WideningM (PermExpr a)

-- If both sides are equal, return one of the sides
widenExpr' _ e1 e2 | e1 == e2 = return e1

-- If both sides are variables, look up their permissions and whether they have
-- been visited and use that information to decide what to do
widenExpr' tp e1@(asVarOffset -> Just (x1, off1)) e2@(asVarOffset ->
                                                     Just (x2, off2)) =
  do p1 <- getVarPermM x1
     p2 <- getVarPermM x2
     isv1 <- isVisitedM x1
     isv2 <- isVisitedM x2
     case (p1, p2, isv1, isv2) of

       -- If we have the same variable with the same offsets (it can avoid the
       -- case above of e1 == e2 if the offsets are offsetsEq but not ==) then
       -- we are done, though we do want to visit the variable
       _ | x1 == x2 && offsetsEq off1 off2 ->
           visitM x1 >> return e1

       -- If we have the same variable but different offsets, then the two sides
       -- cannot be equal, so we generalize with a new variable
       _ | x1 == x2 ->
           do x <- bindFreshVar tp
              visitM x
              ((p1',p2'), p') <-
                doubleSplitWidenPerm tp (offsetPerm off1 p1) (offsetPerm off2 p2)
              setOffVarPermM x1 off1 p1'
              setOffVarPermM x2 off2 p2'
              setVarPermM x p'
              return $ PExpr_Var x

       -- If a variable has an eq(e) permission, replace it with e and recurse
       (ValPerm_Eq e1', _, _, _) ->
         visitM x1 >> widenExpr tp (offsetExpr off1 e1') e2
       (_, ValPerm_Eq e2', _, _) ->
         visitM x2 >> widenExpr tp e1 (offsetExpr off2 e2')

       -- If both variables have been visited and are not equal and do not have
       -- eq permissions, then they are equal to different locations elsewhere
       -- in our widening, and so this location should not be equated to either
       -- of them; thus we make a fresh variable
       (_, _, True, True) ->
         do x <- bindFreshVar tp
            visitM x
            ((p1',p2'), p') <-
              doubleSplitWidenPerm tp (offsetPerm off1 p1) (offsetPerm off2 p2)
            setOffVarPermM x1 off1 p1'
            setOffVarPermM x2 off2 p2'
            setVarPermM x p'
            return $ PExpr_Var x

       -- If only one variable has been visited, its perms need to be split
       -- between its other location(s) and here
       (_, _, True, _) ->
         do (p1', p2') <-
              splitWidenPerm tp (offsetPerm off1 p1) (offsetPerm off2 p2)
            setVarPermM x1 (offsetPerm (negatePermOffset off1) p1')
            setVarPermM x2 (offsetPerm (negatePermOffset off2) p2')
            return e2
       (_, _, _, True) ->
         do (p2', p1') <-
              splitWidenPerm tp (offsetPerm off2 p2) (offsetPerm off1 p2)
            setVarPermM x1 (offsetPerm (negatePermOffset off1) p1')
            setVarPermM x2 (offsetPerm (negatePermOffset off2) p2')
            return e1

       -- If we get here, then neither x1 nor x2 has been visited, so choose x1,
       -- set x2 equal to x1 &+ (off1 - off2), and set x1's permissions to be
       -- the result of widening p1 against p2
       _ ->
         do visitM x1 >> visitM x2
            setVarPermM x2 (ValPerm_Eq $
                            offsetExpr (addPermOffsets off1 $
                                        negatePermOffset off2) $ PExpr_Var x1)
            p' <- widenPerm tp (offsetPerm off1 p1) (offsetPerm off2 p2)
            setVarPermM x1 (offsetPerm (negatePermOffset off1) p')
            return e1


-- If one side is a variable x and the other is not, then the non-variable side
-- cannot have any permissions, and there are fewer cases than the above
widenExpr' tp (asVarOffset -> Just (x1, off1)) e2 =
  do p1 <- getVarPermM x1
     case p1 of

       -- If x1 has an eq(e) permission, replace it with e and recurse
       ValPerm_Eq e1' ->
         visitM x1 >> widenExpr tp (offsetExpr off1 e1') e2

       -- Otherwise bind a fresh variable, because even if x1 has not been
       -- visited before, it could still occur somewhere we haven't visited yet
       _ ->
         do x <- bindFreshVar tp
            visitM x
            return $ PExpr_Var x

-- Similar to the previous case, but with the variable on the right
widenExpr' tp e1 (asVarOffset -> Just (x2, off2)) =
  do p2 <- getVarPermM x2
     case p2 of

       -- If x2 has an eq(e) permission, replace it with e and recurse
       ValPerm_Eq e2' ->
         visitM x2 >> widenExpr tp e1 (offsetExpr off2 e2')

       -- Otherwise bind a fresh variable, because even if x1 has not been
       -- visited before, it could still occur somewhere we haven't visited yet
       _ ->
         do x <- bindFreshVar tp
            visitM x
            return $ PExpr_Var x

-- Widen two structs by widening their contents
widenExpr' (StructRepr tps) (PExpr_Struct es1) (PExpr_Struct es2) =
  PExpr_Struct <$> widenExprs (mkCruCtx tps) es1 es2

-- Widen llvmwords by widening the words
widenExpr' (LLVMPointerRepr w) (PExpr_LLVMWord e1) (PExpr_LLVMWord e2) =
  PExpr_LLVMWord <$> widenExpr (BVRepr w) e1 e2

-- Widen named shapes with the same names
--
-- FIXME: we currently only handle shapes with no modalities, because the
-- modalities only come about when proving equality shapes, which themselves are
-- only really used by memcpy and similar functions
widenExpr' _ (PExpr_NamedShape Nothing Nothing nmsh1 args1)
  (PExpr_NamedShape Nothing Nothing nmsh2 args2)
  | Just (Refl,Refl) <- namedShapeEq nmsh1 nmsh2 =
    PExpr_NamedShape Nothing Nothing nmsh1 <$>
    widenExprs (namedShapeArgs nmsh1) args1 args2

widenExpr' (LLVMShapeRepr w) (PExpr_EqShape e1) (PExpr_EqShape e2) =
  PExpr_EqShape <$> widenExpr (LLVMBlockRepr w) e1 e2

widenExpr' tp (PExpr_PtrShape Nothing Nothing sh1)
  (PExpr_PtrShape Nothing Nothing sh2) =
  PExpr_PtrShape Nothing Nothing <$> widenExpr tp sh1 sh2

widenExpr' _ (PExpr_FieldShape (LLVMFieldShape p1)) (PExpr_FieldShape
                                                    (LLVMFieldShape p2))
  | Just Refl <- testEquality (exprLLVMTypeWidth p1) (exprLLVMTypeWidth p2) =
    PExpr_FieldShape <$> LLVMFieldShape <$> widenPerm knownRepr p1 p2

-- Array shapes can only be widened if they have the same length, stride, and
-- fields whose ith fields have the same size for each i
widenExpr' _ (PExpr_ArrayShape len1 stride1 flds1) (PExpr_ArrayShape
                                                   len2 stride2 flds2)
  | bvEq len1 len2 && stride1 == stride2
  , and (zipWith
         (\(LLVMFieldShape p1) (LLVMFieldShape p2) ->
           isJust $ testEquality (exprLLVMTypeWidth p1) (exprLLVMTypeWidth p2))
         flds1 flds2) =
    PExpr_ArrayShape len1 stride1 <$>
    zipWithM (\(LLVMFieldShape p1) (LLVMFieldShape p2) ->
               case testEquality (exprLLVMTypeWidth p1) (exprLLVMTypeWidth p2) of
                 Just Refl -> LLVMFieldShape <$> widenPerm knownRepr p1 p2
                 Nothing -> error "widenExpr: unreachable!")
    flds1 flds2

-- FIXME: there should be some check that the first shapes have the same length,
-- though this is more complex if they might have free variables...?
widenExpr' tp (PExpr_SeqShape sh1 sh1') (PExpr_SeqShape sh2 sh2') =
  PExpr_SeqShape <$> widenExpr tp sh1 sh2 <*> widenExpr tp sh1' sh2'

widenExpr' tp (PExpr_OrShape sh1 sh1') (PExpr_OrShape sh2 sh2') =
  PExpr_OrShape <$> widenExpr tp sh1 sh2 <*> widenExpr tp sh1' sh2'

widenExpr' tp (PExpr_ExShape mb_sh1) sh2 =
  do x <- bindFreshVar knownRepr
     widenExpr tp (varSubst (singletonVarSubst x) mb_sh1) sh2

widenExpr' tp sh1 (PExpr_ExShape mb_sh2) =
  do x <- bindFreshVar knownRepr
     widenExpr tp sh1 (varSubst (singletonVarSubst x) mb_sh2)

-- NOTE: this assumes that permission expressions only occur in covariant
-- positions
widenExpr' (ValuePermRepr tp) (PExpr_ValPerm p1) (PExpr_ValPerm p2) =
  PExpr_ValPerm <$> widenPerm tp p1 p2

-- Default case: widen two unequal expressions by making a fresh output
-- existential variable, which could be equal to either
widenExpr' tp _ _ =
  do x <- bindFreshVar tp
     visitM x
     return $ PExpr_Var x


-- | Widen a sequence of expressions
widenExprs :: CruCtx tps -> PermExprs tps -> PermExprs tps ->
              WideningM (PermExprs tps)
widenExprs _ MNil MNil = return MNil
widenExprs (CruCtxCons tps tp) (es1 :>: e1) (es2 :>: e2) =
  (:>:) <$> widenExprs tps es1 es2 <*> widenExpr tp e1 e2


-- | Take two block permissions @bp1@ and @bp2@ whose ranges overlap and use
-- 'splitLLVMBlockPerm' to remove any parts of them that do not overlap,
-- returning some @bp1'@ and @bp2'@ with the same range, along with additional
-- portions of @bp1@ and @bp2@ that were removed
equalizeLLVMBlockRanges :: (1 <= w, KnownNat w) =>
                           LLVMBlockPerm w -> LLVMBlockPerm w ->
                           Maybe (LLVMBlockPerm w, LLVMBlockPerm w,
                                  [LLVMBlockPerm w], [LLVMBlockPerm w])
equalizeLLVMBlockRanges bp1 bp2
  | bvEq (llvmBlockOffset bp1) (llvmBlockOffset bp2)
  , bvEq (llvmBlockLen bp1) (llvmBlockLen bp2) =
    return (bp1, bp2, [], [])
equalizeLLVMBlockRanges bp1 bp2
  | bvEq (llvmBlockOffset bp1) (llvmBlockOffset bp2)
  , bvLeq (llvmBlockLen bp1) (llvmBlockLen bp2) =
    do (bp2', bp2'') <- splitLLVMBlockPerm (bvAdd (llvmBlockOffset bp1)
                                            (llvmBlockLen bp1)) bp2
       return (bp1, bp2', [], [bp2''])
equalizeLLVMBlockRanges bp1 bp2
  | bvEq (llvmBlockOffset bp1) (llvmBlockOffset bp2)
  , bvLeq (llvmBlockLen bp2) (llvmBlockLen bp1) =
    do (bp1', bp1'') <- splitLLVMBlockPerm (bvAdd (llvmBlockOffset bp2)
                                            (llvmBlockLen bp2)) bp1
       return (bp1', bp2, [bp1''], [])
equalizeLLVMBlockRanges bp1 bp2
  | bvLeq (llvmBlockOffset bp1) (llvmBlockOffset bp2) =
    do (bp1', bp1'') <- splitLLVMBlockPerm (llvmBlockOffset bp2) bp1
       (bp1_ret, bp2_ret, bps1, bps2) <- equalizeLLVMBlockRanges bp1'' bp2
       return (bp1_ret, bp2_ret, bp1':bps1, bps2)
equalizeLLVMBlockRanges bp1 bp2
  | bvLeq (llvmBlockOffset bp2) (llvmBlockOffset bp1) =
    do (bp2', bp2'') <- splitLLVMBlockPerm (llvmBlockOffset bp1) bp2
       (bp1_ret, bp2_ret, bps1, bps2) <- equalizeLLVMBlockRanges bp1 bp2''
       return (bp1_ret, bp2_ret, bps1, bp2':bps2)
equalizeLLVMBlockRanges _ _ = Nothing


-- | Widen two block permissions against each other, assuming they already have
-- the same range
widenBlockPerm :: (1 <= w, KnownNat w) => LLVMBlockPerm w -> LLVMBlockPerm w ->
                  WideningM (LLVMBlockPerm w)
widenBlockPerm bp1 bp2 =
  LLVMBlockPerm <$>
  widenExpr knownRepr (llvmBlockRW bp1) (llvmBlockRW bp2) <*>
  widenExpr knownRepr (llvmBlockLifetime bp1) (llvmBlockLifetime bp2) <*>
  return (llvmBlockOffset bp1) <*> return (llvmBlockLen bp1) <*>
  widenExpr knownRepr (llvmBlockShape bp1) (llvmBlockShape bp2)


-- | Widen a sequence of atomic permissions against each other
widenAtomicPerms :: TypeRepr a -> [AtomicPerm a] -> [AtomicPerm a] ->
                    WideningM [AtomicPerm a]

-- If one side is empty, we return the empty list, i.e., true
widenAtomicPerms _ [] _ = return []
widenAtomicPerms _ _ [] = return []

-- If there is a permission on the right that equals p1, use p1, and recursively
-- widen the remaining permissions
widenAtomicPerms tp (p1 : ps1) ps2
  | Just i <- findIndex (== p1) ps2 =
    (p1 :) <$> widenAtomicPerms tp ps1 (deleteNth i ps2)

-- If the first permission on the left is an LLVM permission overlaps with some
-- permission on the right, widen these against each other
widenAtomicPerms tp@(LLVMPointerRepr w) (p1 : ps1) ps2
  | Just bp1 <- llvmAtomicPermToBlock p1
  , rng1 <- llvmBlockRange bp1
  , Just i <-
      withKnownNat w (findIndex ((== Just True) . fmap (bvRangesOverlap rng1)
                                 . llvmAtomicPermRange) ps2)
  , Just bp2 <- llvmAtomicPermToBlock (ps2!!i)
  , Just (bp1', bp2', bps1_rem, bps2_rem) <-
      withKnownNat w (equalizeLLVMBlockRanges bp1 bp2)
  = withKnownNat w (
      (:) <$> (Perm_LLVMBlock <$> widenBlockPerm bp1' bp2') <*>
      widenAtomicPerms tp (map Perm_LLVMBlock bps1_rem ++ ps1)
      (map Perm_LLVMBlock bps2_rem ++ deleteNth i ps2))

-- Default: cannot widen p1 against any p2 on the right, so drop it and recurse
widenAtomicPerms tp (_ : ps1) ps2 = widenAtomicPerms tp ps1 ps2


-- | Widen permissions against each other
widenPerm :: TypeRepr a -> ValuePerm a -> ValuePerm a -> WideningM (ValuePerm a)
widenPerm tp p1 p2 =
  traceM (\i ->
           fillSep [pretty "widenPerm", permPretty i p1, permPretty i p2]) >>
  widenPerm' tp p1 p2

widenPerm' :: TypeRepr a -> ValuePerm a -> ValuePerm a ->
              WideningM (ValuePerm a)

widenPerm' tp (ValPerm_Eq e1) (ValPerm_Eq e2) =
  ValPerm_Eq <$> widenExpr tp e1 e2

widenPerm' tp (ValPerm_Eq (asVarOffset -> Just (x1, off1))) p2 =
  do p1 <- getVarPermM x1
     isv1 <- isVisitedM x1
     case (p1, isv1) of
       (ValPerm_Eq e1, _) ->
         visitM x1 >> widenPerm tp (ValPerm_Eq $ offsetExpr off1 e1) p2
       (_, False) ->
         do visitM x1
            p1' <- widenPerm tp (offsetPerm off1 p1) p2
            setVarPermM x1 (offsetPerm (negatePermOffset off1) p1')
            return (ValPerm_Eq $ offsetExpr off1 $ PExpr_Var x1)
       (_, True) ->
         do x <- bindFreshVar tp
            visitM x
            (p1', p1'') <- splitWidenPerm tp (offsetPerm off1 p1) p2
            setVarPermM x1 p1'
            setVarPermM x p1''
            return (ValPerm_Eq $ PExpr_Var x)

widenPerm' tp p1 (ValPerm_Eq (asVarOffset -> Just (x2, off2))) =
  do p2 <- getVarPermM x2
     isv2 <- isVisitedM x2
     case (p2, isv2) of
       (ValPerm_Eq e2, _) ->
         visitM x2 >> widenPerm tp p1 (ValPerm_Eq $ offsetExpr off2 e2)
       (_, False) ->
         do visitM x2
            p2' <- widenPerm tp p1 (offsetPerm off2 p2)
            setVarPermM x2 (offsetPerm (negatePermOffset off2) p2')
            return (ValPerm_Eq $ offsetExpr off2 $ PExpr_Var x2)
       (_, True) ->
         do x <- bindFreshVar tp
            visitM x
            (p2', p2'') <- splitWidenPerm tp (offsetPerm off2 p2) p1
            setVarPermM x2 p2'
            setVarPermM x p2''
            return (ValPerm_Eq $ PExpr_Var x)

widenPerm' tp (ValPerm_Or p1 p1') (ValPerm_Or p2 p2') =
  ValPerm_Or <$> widenPerm tp p1 p2 <*> widenPerm tp p1' p2'
widenPerm' tp (ValPerm_Exists mb_p1) p2 =
  do x <- bindFreshVar knownRepr
     widenPerm tp (varSubst (singletonVarSubst x) mb_p1) p2
widenPerm' tp p1 (ValPerm_Exists mb_p2) =
  do x <- bindFreshVar knownRepr
     widenPerm tp p1 (varSubst (singletonVarSubst x) mb_p2)
widenPerm' _ (ValPerm_Named npn1 args1 off1) (ValPerm_Named npn2 args2 off2)
  | Just (Refl, Refl, Refl) <- testNamedPermNameEq npn1 npn2
  , offsetsEq off1 off2 =
    (\args -> ValPerm_Named npn1 args off1) <$>
    widenExprs (namedPermNameArgs npn1) args1 args2
widenPerm' _ (ValPerm_Var x1 off1) (ValPerm_Var x2 off2)
  | x1 == x2 && offsetsEq off1 off2 = return $ ValPerm_Var x1 off1
widenPerm' tp (ValPerm_Conj ps1) (ValPerm_Conj ps2) =
  ValPerm_Conj <$> widenAtomicPerms tp ps1 ps2
widenPerm' _ _ _ = return ValPerm_True


-- | Widen a sequence of permissions
widenPerms :: CruCtx tps -> ValuePerms tps -> ValuePerms tps ->
              WideningM (ValuePerms tps)
widenPerms _ MNil MNil = return MNil
widenPerms (CruCtxCons tps tp) (ps1 :>: p1) (ps2 :>: p2) =
  (:>:) <$> widenPerms tps ps1 ps2 <*> widenPerm tp p1 p2


----------------------------------------------------------------------
-- * Top-Level Entrypoints
----------------------------------------------------------------------

-- | A sequence of permissions on some regular and ghost arguments
data ArgVarPerms args vars =
  ArgVarPerms { wideningVars :: CruCtx vars,
                wideningPerms :: MbValuePerms (args :++: vars) }

$(mkNuMatching [t| forall args vars. ArgVarPerms args vars |])

completeMbArgVarPerms :: CruCtx vars ->
                         Mb (args :++: vars) (ExtVarPerms (args :++: vars)) ->
                         Some (ArgVarPerms args)
completeMbArgVarPerms vars (mbMatch -> [nuMP| ExtVarPerms_Base ps |]) =
  Some $ ArgVarPerms vars ps
completeMbArgVarPerms vars (mbMatch ->
                            [nuMP| ExtVarPerms_Mb var mb_ext_wid |]) =
  completeMbArgVarPerms (CruCtxCons vars (mbLift var)) (mbCombine mb_ext_wid)

completeArgVarPerms :: Mb args (ExtVarPerms args) -> Some (ArgVarPerms args)
completeArgVarPerms = completeMbArgVarPerms CruCtxNil

{-
completeWideningM :: CruCtx args -> MbValuePerms args -> Mb args (WideningM ()) ->
                     Some (Widening args)
completeWideningM args mb_arg_perms mb_m =
  widMapWidening args $
  flip nuMultiWithElim (MNil :>: mb_m :>: mb_arg_perms) $
  \ns (_ :>: Identity m :>: Identity arg_perms) ->
  unWideningM m $ wnMapFromPerms ns arg_perms
-}

rlMap2ToList :: (forall a. f a -> g a -> c) -> RAssign f ctx ->
                RAssign g ctx -> [c]
rlMap2ToList _ MNil MNil = []
rlMap2ToList f (xs :>: x) (ys :>: y) = rlMap2ToList f xs ys ++ [f x y]

-- | Extend the context of a name-binding on the left with multiple types
extMbMultiL :: RAssign f ctx1 -> Mb ctx2 a -> Mb (ctx1 :++: ctx2) a
extMbMultiL ns mb = mbCombine $ nuMulti ns $ const mb

mbSeparatePrx :: prx ctx1 -> RAssign any ctx2 -> Mb (ctx1 :++: ctx2) a ->
                 Mb ctx1 (Mb ctx2 a)
mbSeparatePrx _ = mbSeparate

-- | Widen two lists of permissions-in-bindings
widen :: CruCtx tops -> CruCtx args -> Some (ArgVarPerms (tops :++: args)) ->
         Some (ArgVarPerms (tops :++: args)) ->
         Some (ArgVarPerms (tops :++: args))
widen tops args (Some (ArgVarPerms vars1 mb_perms1)) (Some (ArgVarPerms
                                                            vars2 mb_perms2)) =
  let all_args = appendCruCtx tops args
      prxs1 = cruCtxProxies vars1
      prxs2 = cruCtxProxies vars2
      mb_mb_perms1 = mbSeparate prxs1 mb_perms1 in
  completeArgVarPerms $ flip nuMultiWithElim1 mb_mb_perms1 $
  \args_ns1 mb_perms1' ->
  (\m -> runWideningM m NameMap.empty args_ns1) $
  do (vars1_ns, ps1) <- openMb vars1 mb_perms1'
     (ns2, ps2) <- openMb (appendCruCtx all_args vars2) mb_perms2
     let (args_ns2, vars2_ns) = RL.split all_args prxs2 ns2
     setVarPermsM (RL.append args_ns1 vars1_ns) ps1
     setVarPermsM ns2 ps2
     let (tops1, locals1) = RL.split tops (cruCtxProxies args) args_ns1
     let (tops2, locals2) = RL.split tops (cruCtxProxies args) args_ns2
     setVarNamesM "topL" tops1
     setVarNamesM "topR" tops2
     setVarNamesM "localL" locals1
     setVarNamesM "localR" locals2
     setVarNamesM "varL" vars1_ns
     setVarNamesM "varR" vars2_ns
     let dist_ps1 = RL.map2 VarAndPerm (RL.append args_ns1 vars1_ns) ps1
     let dist_ps2 = RL.map2 VarAndPerm ns2 ps2
     traceM (\i ->
              pretty "Widening" <> line <>
              indent 2 (permPretty i dist_ps1) <> line <>
              pretty "Against" <> line <>
              indent 2 (permPretty i dist_ps2))
     void $ widenExprs all_args (RL.map PExpr_Var args_ns1) (RL.map
                                                             PExpr_Var args_ns2)
     wnmap <- view wsNameMap <$> get
     traceM (\i ->
              pretty "Widening returning:" <> line <>
              indent 2 (fillSep $
                        map (\(NameAndElem x (Pair p _)) ->
                              permPretty i x <> colon <> permPretty i p) $
                        NameMap.assocs wnmap))
     return ()
