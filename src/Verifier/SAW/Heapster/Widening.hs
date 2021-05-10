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
import Data.Functor.Constant
import Data.Functor.Product
import Control.Monad.State
import Control.Monad.Cont
import Control.Lens hiding ((:>), Index, Empty, ix, op)

import Data.Parameterized.Some

import Lang.Crucible.LLVM.MemModel
import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits
import Data.Binding.Hobbits.NameMap (NameMap)
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Lang.Crucible.Types


----------------------------------------------------------------------
-- * The Widening Monad
----------------------------------------------------------------------

-- | A 'Widening' for some list of variables that extends @vars@
data ExtWidening vars
  = ExtWidening_Base (ValuePerms vars)
  | forall var. ExtWidening_Mb (TypeRepr var) (Binding var
                                               (ExtWidening (vars :> var)))

$(mkNuMatching [t| forall vars. ExtWidening vars |])

extWidening_MbMulti :: CruCtx ctx -> Mb ctx (ExtWidening (vars :++: ctx)) ->
                       ExtWidening vars
extWidening_MbMulti CruCtxNil mb_ewid = elimEmptyMb mb_ewid
extWidening_MbMulti (CruCtxCons ctx tp) mb_ewid =
  extWidening_MbMulti ctx $
  fmap (ExtWidening_Mb tp) $ mbSeparate (MNil :>: Proxy) mb_ewid

newtype ExtWideningFun vars =
  ExtWideningFun { applyExtWideningFun ::
                     RAssign Name vars -> ExtWidening vars }

type WidNameMap = NameMap (Product ValuePerm (Constant Bool))

{-
wnMapIns :: Name a -> ValuePerm a -> WidNameMap -> WidNameMap
wnMapIns n p = NameMap.insert n (Pair p (Constant False))

wnMapFromPerms :: RAssign Name ps -> RAssign ValuePerm ps -> WidNameMap
wnMapFromPerms ns ps =
  RL.foldr (\(Pair n p) -> wnMapIns n p) NameMap.empty $
  RL.map2 Pair ns ps

wnMapFromPermsVisiteds :: RAssign Name ps -> RAssign ValuePerm ps ->
                          RAssign (Constant Bool) ps ->
                          WidNameMap
wnMapFromPermsVisiteds = error "FIXME HERE NOW"
-}

-- | Look up the permission for a name in a 'WidNameMap'
wnMapGetPerm :: Name a -> WidNameMap -> ValuePerm a
wnMapGetPerm n nmap | Just (Pair p _) <- NameMap.lookup n nmap = p
wnMapGetPerm _ _ = ValPerm_True

wnMapExtWidFun :: WidNameMap -> ExtWideningFun vars
wnMapExtWidFun wnmap =
  ExtWideningFun $ \ns -> ExtWidening_Base $ RL.map (flip wnMapGetPerm wnmap) ns

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

type WideningM =
  StateT WidNameMap (PolyContT ExtWideningFun Identity)

runWideningM :: WideningM () -> WidNameMap -> RAssign Name args ->
                ExtWidening args
runWideningM m wnmap =
  applyExtWideningFun $ runIdentity $
  runPolyContT (runStateT m wnmap) (Identity . wnMapExtWidFun . snd)

openMb :: CruCtx ctx -> Mb ctx a -> WideningM (RAssign Name ctx, a)
openMb ctx mb_a =
  lift $ PolyContT $ \k -> Identity $ ExtWideningFun $ \ns ->
  extWidening_MbMulti ctx $
  mbMap2 (\ns' a ->
           applyExtWideningFun (runIdentity $ k (ns',a)) (RL.append ns ns'))
  (nuMulti (cruCtxProxies ctx) id) mb_a

bindFreshVar :: TypeRepr tp -> WideningM (ExprVar tp)
bindFreshVar tp = snd <$> openMb (singletonCruCtx tp) (nu id)

visitM :: ExprVar a -> WideningM ()
visitM n =
  modify $ flip NameMap.alter n $ \case
  Just (Pair p _) -> Just (Pair p (Constant True))
  Nothing -> Just (Pair ValPerm_True (Constant True))

isVisitedM :: ExprVar a -> WideningM Bool
isVisitedM n =
  maybe False (\(Pair _ (Constant b)) -> b) <$> NameMap.lookup n <$> get

getVarPermM :: ExprVar a -> WideningM (ValuePerm a)
getVarPermM n = wnMapGetPerm n <$> get

setVarPermM :: ExprVar a -> ValuePerm a -> WideningM ()
setVarPermM = error "FIXME HERE NOW"

-- | Set the permissions for @x &+ off@ to @p@, by setting the permissions for
-- @x@ to @p - off@
setOffVarPermM :: ExprVar a -> PermOffset a -> ValuePerm a -> WideningM ()
setOffVarPermM x off p =
  setVarPermM x (offsetPerm (negatePermOffset off) p)

setVarPermsM :: RAssign Name ctx -> RAssign ValuePerm ctx -> WideningM ()
setVarPermsM = error "FIXME HERE NOW"


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


widenExpr :: TypeRepr a -> PermExpr a -> PermExpr a -> WideningM (PermExpr a)

-- If both sides are equal, return one of the sides
widenExpr tp e1 e2 | e1 == e2 = return e1

-- If both sides are variables, look up their permissions and whether they have
-- been visited and use that information to decide what to do
widenExpr tp e1@(asVarOffset -> Just (x1, off1)) e2@(asVarOffset ->
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
              ((p1,p2), p') <-
                doubleSplitWidenPerm tp (offsetPerm off1 p1) (offsetPerm off2 p2)
              setOffVarPermM x1 off1 p1
              setOffVarPermM x2 off2 p2
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
       (p1, p2, True, True) ->
         do x <- bindFreshVar tp
            visitM x
            ((p1,p2), p') <-
              doubleSplitWidenPerm tp (offsetPerm off1 p1) (offsetPerm off2 p2)
            setOffVarPermM x1 off1 p1
            setOffVarPermM x2 off2 p2
            setVarPermM x p'
            return $ PExpr_Var x

       -- If only one variable has been visited, its perms need to be split
       -- between its other location(s) and here
       (p1, p2, True, _) ->
         do (p1', p2') <-
              splitWidenPerm tp (offsetPerm off1 p1) (offsetPerm off2 p2)
            setVarPermM x1 (offsetPerm (negatePermOffset off1) p1')
            setVarPermM x2 (offsetPerm (negatePermOffset off2) p2')
            return e2
       (p1, p2, _, True) ->
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
widenExpr tp e1@(asVarOffset -> Just (x1, off1)) e2 =
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
widenExpr tp e1 e2@(asVarOffset -> Just (x2, off2)) =
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
widenExpr (StructRepr tps) (PExpr_Struct es1) (PExpr_Struct es2) =
  PExpr_Struct <$> widenExprs (mkCruCtx tps) es1 es2

-- Widen llvmwords by widening the words
widenExpr (LLVMPointerRepr w) (PExpr_LLVMWord e1) (PExpr_LLVMWord e2) =
  PExpr_LLVMWord <$> widenExpr (BVRepr w) e1 e2

-- Default case: widen two unequal expressions by making a fresh output
-- existential variable, which could be equal to either
widenExpr tp _ _ =
  do x <- bindFreshVar tp
     visitM x
     return $ PExpr_Var x


-- | Widen a sequence of expressions
widenExprs :: CruCtx tps -> PermExprs tps -> PermExprs tps ->
              WideningM (PermExprs tps)
widenExprs _ MNil MNil = return MNil
widenExprs (CruCtxCons tps tp) (es1 :>: e1) (es2 :>: e2) =
  (:>:) <$> widenExprs tps es1 es2 <*> widenExpr tp e1 e2


-- | Widen a sequence of atomic permissions against each other
widenAtomicPerms :: TypeRepr tp -> [AtomicPerm a] -> [AtomicPerm a] ->
                    WideningM [AtomicPerm a]
widenAtomicPerms = error "FIXME HERE NOW"

-- | Widen permissions against each other
widenPerm :: TypeRepr a -> ValuePerm a -> ValuePerm a -> WideningM (ValuePerm a)
widenPerm tp (ValPerm_Eq e1) (ValPerm_Eq e2) =
  ValPerm_Eq <$> widenExpr tp e1 e2
widenPerm tp (ValPerm_Eq (asVarOffset -> Just (x1, off1))) p2 =
  error "FIXME HERE NOW"
widenPerm tp p1 (ValPerm_Eq (asVarOffset -> Just (x2, off2))) =
  error "FIXME HERE NOW"

widenPerm tp (ValPerm_Or p1 p1') (ValPerm_Or p2 p2') =
  ValPerm_Or <$> widenPerm tp p1 p2 <*> widenPerm tp p1' p2'
widenPerm tp (ValPerm_Exists mb_p1) p2 =
  do x <- bindFreshVar knownRepr
     widenPerm tp (varSubst (singletonVarSubst x) mb_p1) p2
widenPerm tp p1 (ValPerm_Exists mb_p2) =
  do x <- bindFreshVar knownRepr
     widenPerm tp p1 (varSubst (singletonVarSubst x) mb_p2)
widenPerm tp (ValPerm_Named npn1 args1 off1) (ValPerm_Named npn2 args2 off2)
  | Just (Refl, Refl, Refl) <- testNamedPermNameEq npn1 npn2
  , offsetsEq off1 off2 =
    (\args -> ValPerm_Named npn1 args off1) <$>
    widenExprs (namedPermNameArgs npn1) args1 args2
widenPerm tp (ValPerm_Var x1 off1) (ValPerm_Var x2 off2)
  | x1 == x2 && offsetsEq off1 off2 = return $ ValPerm_Var x1 off1
widenPerm tp (ValPerm_Conj ps1) (ValPerm_Conj ps2) =
  ValPerm_Conj <$> widenAtomicPerms tp ps1 ps2
widenPerm _ _ _ = return ValPerm_True


-- | Widen a sequence of permissions
widenPerms :: CruCtx tps -> ValuePerms tps -> ValuePerms tps ->
              WideningM (ValuePerms tps)
widenPerms _ MNil MNil = return MNil
widenPerms (CruCtxCons tps tp) (ps1 :>: p1) (ps2 :>: p2) =
  (:>:) <$> widenPerms tps ps1 ps2 <*> widenPerm tp p1 p2


{-
{-
class WidUnify a where
  widUnify' :: RAssign prx vars -> MatchedMb (vars1 :++: vars) a ->
               MatchedMb (vars2 :++: vars) a ->
               WideningM args vars1 vars2 (Mb vars a)

widUnify :: WidUnify a => RAssign prx vars -> Mb (vars1 :++: vars) a ->
            Mb (vars2 :++: vars) a -> WideningM args vars1 vars2 (Mb vars a)
widUnify vars mb1 mb2 = widUnify' vars (mbMatch mb1) (mbMatch mb2)

instance WideningUnify (PermExpr a) where
  widUnify' = error "FIXME HERE NOW"
-}

{-
-- | The generic function for widening on matched name-bindings
class WidenM a where
  widenM' :: KnownCruCtx vars -> MatchedMb (vars1 :++: vars) a ->
             MatchedMb (vars2 :++: vars) a ->
             WideningM args vars1 vars2 (Mb vars a)

-- | Apply widening to two objects in bindings
widenM :: WidenM a => KnownCruCtx vars -> Mb (vars1 :++: vars) a ->
          Mb (vars2 :++: vars) a ->
          WideningM args vars1 vars2 (Mb vars a)
widenM vars mb1 mb2 = widenM' vars (mbMatch mb1) (mbMatch mb2)
-}

-- | Convert an expression to a variable + offset, in a binding, if possible
asMbVarOffset :: MatchedMb ctx (PermExpr a) ->
                 Maybe (Mb ctx (ExprVar a), Mb ctx (PermOffset a))
asMbVarOffset [nuMP| PExpr_Var mb_x |] =
  Just (mb_x, fmap (const NoPermOffset) mb_x)
asMbVarOffset [nuMP| PExpr_LLVMOffset mb_x mb_off |] =
  Just (mb_x, fmap LLVMPermOffset mb_off)
asMbVarOffset _ = Nothing

-- | Test if a 'Member' proof in an appended list @ctx1 :++: ctx2@ is a proof of
-- membership in the first or second list
memberAppendCase :: Proxy ctx1 -> RAssign prx ctx2 -> Member (ctx1 :++: ctx2) a ->
                    Either (Member ctx1 a) (Member ctx2 a)
memberAppendCase _ MNil memb = Left memb
memberAppendCase _ (_ :>: _) Member_Base = Right Member_Base
memberAppendCase ctx1 (ctx2 :>: _) (Member_Step memb) =
  case memberAppendCase ctx1 ctx2 memb of
    Left ret -> Left ret
    Right ret -> Right $ Member_Step ret

-- | Test if an expression in a binding for top-level and local evars is a
-- top-level evar plus an optional offset
asMbTopEVarOffset :: KnownCruCtx vars -> Mb (evars :++: vars) (PermExpr a) ->
                     Maybe (Member evars a, Mb (evars :++: vars) (PermOffset a))
asMbTopEVarOffset vars mb_e
  | Just (mb_x, mb_off) <- asMbVarOffset (mbMatch mb_e)
  , Left memb <- mbNameBoundP mb_x
  , Left memb_evars <- memberAppendCase Proxy vars memb =
    Just (memb_evars, mb_off)
asMbTopEVarOffset _ _ = Nothing

-- | Helper function to make a multi-binding using a 'CruCtx'
mbCtx :: CruCtx ctx -> (RAssign Name ctx -> a) -> Mb ctx a
mbCtx ctx = nuMulti (cruCtxProxies ctx)

-- | FIXME HERE NOW: documentation
widenPerm :: KnownCruCtx vars -> TypeRepr a ->
             Mb (vars1 :++: vars) (ValuePerm a) ->
             Mb (vars2 :++: vars) (ValuePerm a) ->
             WideningM args vars1 vars2 (Mb vars (ValuePerm a))

-- If both sides are of the form eq(x &+ off) for top-level evars x...
widenPerm vars tp [nuP| ValPerm_Eq mb_e1 |] [nuP| ValPerm_Eq mb_e2 |]
  | Just (evar1, mb_off1) <- asMbTopEVarOffset vars mb_e1
  , Just (evar2, mb_off2) <- asMbTopEVarOffset vars mb_e2 =
    do maybe_e1 <- psubstEVarsLiftM TpMux1 vars mb_e1
       maybe_e2 <- psubstEVarsLiftM TpMux2 vars mb_e2
       isset_evar1 <- inputEVarIsSetM TpMux1 evar1
       isset_evar2 <- inputEVarIsSetM TpMux2 evar2
       maybe_off1 <- psubstEVarsLiftM TpMux1 vars mb_off1
       maybe_off2 <- psubstEVarsLiftM TpMux2 vars mb_off2

       case (maybe_e1, maybe_e2) of
         -- If we can substitute into both sides to get some e1==e2, return e1
         (Just e1, Just e2)
           | e1 == e2 -> return $ nuMulti vars $ const $ ValPerm_Eq e1

         -- FIXME: if one side is a set evar and the other is an unset evar,
         -- that means that the side whose evar is set has more equalities than
         -- the other. This is equivalent to widening permissions of the form
         -- x:p,y:eq(x) with x:p1,y:p2. There are multiple ways we could widen
         -- this, by either splitting p into pieces that can be widened against
         -- p1 and p2, or by returning something like x:p1', y:(eq(x) or p2').
         -- Right now, we don't do either, and just give up...

         -- If we can substitute into the LHS to get some e1 and the RHS is an
         -- unset evar x2 with known offset off2, set x2=e1-off2 and return e1
         {-
         (Just e1, Nothing)
           | not isset_evar2
           , Just off2 <- maybe_off2 ->
             ...

         -- If we can substitute into the RHS to get some e2 and the LHS is an
         -- unset evar x1 with known offset off1, set x1=e2-off1 and return e2
         (Nothing, Just e1)
           | not isset_evar1
           , Just off1 <- maybe_off1 ->
             ...
         -}

         -- If neither evar is set, make a fresh output evar, whose permissions
         -- are given by widening those of the two input evars
         (Nothing, Nothing)
           | not isset_evar1
           , not isset_evar2
           , Just off1 <- maybe_off1
           , Just off2 <- maybe_off2 ->
             do p1 <- getEvarPermsM TpMux1 evar1
                p2 <- getEvarPermsM TpMux2 evar2
                n <- bindWideningVar tp $ fmap elimEmptyMb $
                  widenPerm MNil tp
                  (fmap (offsetPerm off1) p1) (fmap (offsetPerm off2) p2)
                setEVarM TpMux1 evar1 (offsetExpr (negatePermOffset off1) $
                                       PExpr_Var n)
                setEVarM TpMux2 evar2 (offsetExpr (negatePermOffset off2) $
                                       PExpr_Var n)
                return $ nuMulti vars $ const $ ValPerm_Eq $ PExpr_Var n

         -- In any other case, we don't know what to do, so just return true
         _ -> return $ nuMulti vars $ const ValPerm_True


-- If the LHS is of the form eq(x1 &+ off1) for an evar x1...
widenPerm vars tp [nuP| ValPerm_Eq mb_e1 |] mb_p2
  | Just (evar1, mb_off1) <- asMbTopEVarOffset vars mb_e1 =
    do isset_evar1 <- inputEVarIsSetM TpMux1 evar1
       maybe_off1 <- psubstEVarsLiftM TpMux1 vars mb_off1
       case isset_evar1 of

         -- If x1 is not set, create a fresh output evar x for it, whose
         -- permissions are given by widening those of x1 with p2, and return
         -- eq(x) as the permissions for the current location
         False
           | Just off1 <- maybe_off1
           , [nuP| Just p2 |] <- (fmap (partialSubst $ emptyPSubst $
                                        knownCtxToCruCtx vars) $
                                  mbSeparate vars mb_p2) ->
             do p1 <- getEvarPermsM TpMux1 evar1
                n <- bindWideningVar tp $ fmap elimEmptyMb $
                  widenPerm MNil tp (fmap (offsetPerm off1) p1) p2
                setEVarM TpMux1 evar1 (offsetExpr (negatePermOffset off1) $
                                       PExpr_Var n)
                return $ nuMulti vars $ const $ ValPerm_Eq $ PExpr_Var n

         -- FIXME: if x1 is already set, then the LHS has more equalities than
         -- the RHS, so we should think about splitting the permissions on x1,
         -- as discussed above, but we are not for now

         -- All other cases: just give up and return true
         _ -> return $ nuMulti vars $ const ValPerm_True


-- If the RHS is of the form eq(x2 &+ off1) for an evar x2...
widenPerm vars tp mb_p1 [nuP| ValPerm_Eq mb_e2 |]
  | Just (evar2, mb_off2) <- asMbTopEVarOffset vars mb_e2 =
    do isset_evar2 <- inputEVarIsSetM TpMux2 evar2
       maybe_off2 <- psubstEVarsLiftM TpMux2 vars mb_off2
       case isset_evar2 of

         -- If x2 is not set, create a fresh output evar x for it, whose
         -- permissions are given by widening those of x2 with p1, and return
         -- eq(x) as the permissions for the current location
         False
           | Just off2 <- maybe_off2
           , [nuP| Just p1 |] <- (fmap (partialSubst $ emptyPSubst $
                                        knownCtxToCruCtx vars) $
                                  mbSeparate vars mb_p1) ->
             do p2 <- getEvarPermsM TpMux2 evar2
                n <- bindWideningVar tp $ fmap elimEmptyMb $
                  widenPerm MNil tp p1 (fmap (offsetPerm off2) p2)
                setEVarM TpMux2 evar2 (offsetExpr (negatePermOffset off2) $
                                       PExpr_Var n)
                return $ nuMulti vars $ const $ ValPerm_Eq $ PExpr_Var n

         -- FIXME: if x2 is already set, then the RHS has more equalities than
         -- the RHS, so we should think about splitting the permissions on x2,
         -- as discussed above, but we are not for now

         -- All other cases: just give up and return true
         _ -> return $ nuMulti vars $ const ValPerm_True


-- | Widen a sequence of permissions
widenPerms :: KnownCruCtx vars -> CruCtx tps ->
              Mb (vars1 :++: vars) (ValuePerms tps) ->
              Mb (vars2 :++: vars) (ValuePerms tps) ->
              WideningM args vars1 vars2 (Mb vars (ValuePerms tps))
widenPerms vars tps mb_ps1 mb_ps2 =
  widenPerms' vars tps (mbMatch mb_ps1) (mbMatch mb_ps2)

-- | The main worker for 'widenPerms'
--
-- FIXME HERE NOW: should we do permissions with determined vars first?
widenPerms' :: KnownCruCtx vars -> CruCtx tps ->
               MatchedMb (vars1 :++: vars) (ValuePerms tps) ->
               MatchedMb (vars2 :++: vars) (ValuePerms tps) ->
               WideningM args vars1 vars2 (Mb vars (ValuePerms tps))
widenPerms' vars _ [nuMP| MNil |] _ = return $ nuMulti vars $ const MNil
widenPerms' vars (CruCtxCons tps tp) [nuMP| ps1 :>: p1 |] [nuMP| ps2 :>: p2 |] =
  mbMap2 (:>:) <$> widenPerms vars tps ps1 ps2 <*> widenPerm vars tp p1 p2


----------------------------------------------------------------------
-- * Top-Level Entrypoints
----------------------------------------------------------------------
-}

data Widening args vars =
  Widening { wideningVars :: CruCtx vars,
             wideningPerms :: MbValuePerms (args :++: vars) }

$(mkNuMatching [t| forall args vars. Widening args vars |])

completeMbExtWidening :: CruCtx vars ->
                         Mb (args :++: vars) (ExtWidening (args :++: vars)) ->
                         Some (Widening args)
completeMbExtWidening vars (mbMatch -> [nuMP| ExtWidening_Base ps |]) =
  Some $ Widening vars ps
completeMbExtWidening vars (mbMatch ->
                            [nuMP| ExtWidening_Mb var mb_ext_wid |]) =
  completeMbExtWidening (CruCtxCons vars (mbLift var)) (mbCombine mb_ext_wid)

completeExtWidening :: Mb args (ExtWidening args) -> Some (Widening args)
completeExtWidening = completeMbExtWidening CruCtxNil

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

-- | Top-level entrypoint
widen :: CruCtx args -> CruCtx vars1 -> CruCtx vars2 ->
         MbValuePerms (args :++: vars1) ->
         MbValuePerms (args :++: vars2) ->
         Some (Widening args)
widen args vars1 vars2 mb_perms1 mb_perms2 =
  let prxs1 = cruCtxProxies vars1
      prxs2 = cruCtxProxies vars2
      mb_mb_perms1 = mbSeparate prxs1 mb_perms1 in
  completeExtWidening $ flip nuMultiWithElim1 mb_mb_perms1 $
  \args_ns1 mb_perms1' ->
  (\m -> runWideningM m NameMap.empty args_ns1) $
  do (vars1_ns, ps1) <- openMb vars1 mb_perms1'
     (ns2, ps2) <- openMb (appendCruCtx args vars2) mb_perms2
     let (args_ns2, _) = RL.split args prxs2 ns2
     setVarPermsM (RL.append args_ns1 vars1_ns) ps1
     widenExprs args (RL.map PExpr_Var args_ns1) (RL.map PExpr_Var args_ns2)
     return ()
