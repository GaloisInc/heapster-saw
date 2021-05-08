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

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits
import Data.Binding.Hobbits.NameMap (NameMap)
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Lang.Crucible.Types


----------------------------------------------------------------------
-- * A New Widening Monad
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

bindWideningVar :: TypeRepr tp -> WideningM (ExprVar tp)
bindWideningVar tp = snd <$> openMb (singletonCruCtx tp) (nu id)

{-
bindWideningVar :: TypeRepr tp -> WideningM (ExprVar tp)
bindWideningVar tp =
  lift $ PolyContT $ \k -> Identity $ ExtWideningFun $ \ns ->
  ExtWidening_Mb tp $ nu $ \n ->
  applyExtWideningFun (runIdentity $ k n) (ns :>: n)
-}

visitVar :: Name a -> WideningM ()
visitVar n = error "FIXME HERE NOW: what if n has no perms?"

setVarPermM :: Name a -> ValuePerm a -> WideningM ()
setVarPermM = error "FIXME HERE NOW"

setVarPermsM :: RAssign Name ctx -> RAssign ValuePerm ctx -> WideningM ()
setVarPermsM = error "FIXME HERE NOW"

{-
data SomeMbs a
  = NoMbs a
  | forall tp. ConsMb (TypeRepr tp) (Binding tp (SomeMbs a))

instance Functor SomeMbs where
  fmap f m = m >>= return . f

instance Applicative SomeMbs where
  pure = return
  (<*>) = ap

instance Monad SomeMbs where
  return x = NoMbs x
  NoMbs a >>= f = f a
  ConsMb tp mb_m >>= f =
    ConsMb tp $ fmap (>>= f) mb_m

type WidNameMap = NameMap (Product ValuePerm (Constant Bool))

wnMapIns :: Name a -> ValuePerm a -> WidNameMap -> WidNameMap
wnMapIns n p = NameMap.insert n (Pair p (Constant False))

wnMapFromPerms :: RAssign Name ps -> RAssign ValuePerm ps -> WidNameMap
wnMapFromPerms ns ps =
  RL.foldr (\(Pair n p) -> wnMapIns n p) NameMap.empty $
  RL.map2 Pair ns ps

-- | Look up the permission for a name in a 'WidNameMap'
wnMapGetPerm :: Name a -> WidNameMap -> ValuePerm a
wnMapGetPerm n nmap | Just (Pair p _) <- NameMap.lookup n nmap = p
wnMapGetPerm _ _ = ValPerm_True

type WideningM = StateT WidNameMap Cont (SomeMbs )

lookupEVar :: Name a -> WideningM (Maybe (ValuePerm a, Bool))
lookupEVar n =
  fmap (\(Pair p (Constant b)) -> (p,b)) <$> NameMap.lookup n <$> get

data SomeTypedMb a = forall ctx. SomeTypedMb (CruCtx ctx) (Mb ctx a)

instance Functor SomeTypedMb where
  fmap f (SomeTypedMb vars mb_a) = SomeTypedMb vars $ fmap f mb_a

runMbSomeMbs :: NuMatching a => CruCtx vars -> Mb vars (SomeMbs a) ->
                SomeTypedMb a
runMbSomeMbs vars mb_mbs =
  case mbMatch mb_mbs of
    [nuMP| NoMbs mb_a |] -> SomeTypedMb vars mb_a
    [nuMP| ConsMb tp mb_mbs' |] ->
      runMbSomeMbs (CruCtxCons vars $ mbLift tp) $ mbCombine mb_mbs'

runSomeMbs :: SomeMbs a -> SomeTypedMb a
runSomeMbs = runMbSomeMbs CruCtxNil . emptyMb

unWideningM :: WideningM () -> WidNameMap -> SomeTypedMb WidNameMap
unWideningM m nmap =
  fmap snd $ runSomeMbs $ runStateT (runContT m return) nmap
-}

{-
----------------------------------------------------------------------
-- * The Widening Monad
----------------------------------------------------------------------

-- | A 'Widening' for some list of variables that extends @vars@
data ExtWidening args vars
  = ExtWidening_Base (ValuePerms args) (ValuePerms vars)
  | forall var. ExtWidening_Mb (TypeRepr var) (Binding var
                                               (ExtWidening args (vars :> var)))

$(mkNuMatching [t| forall args vars. ExtWidening args vars |])

extMbExtWidening :: prx vars1 -> CruCtx vars2 -> ValuePerm var ->
                    Mb vars2 (ExtWidening args (vars1 :++: vars2)) ->
                    Mb vars2 (ExtWidening args (vars1 :> var :++: vars2))
extMbExtWidening vars1 vars2 p (mbMatch ->
                                [nuMP| ExtWidening_Base mb_arg_ps mb_ps |]) =
  mbMap2 ExtWidening_Base mb_arg_ps $
  flip fmap mb_ps (\ps ->
                    let (ps1, ps2) = RL.split vars1 (cruCtxProxies vars2) ps in
                    RL.append (ps1 :>: p) ps2)
extMbExtWidening vars1 vars2 p (mbMatch ->
                                [nuMP| ExtWidening_Mb mb_tp mb_ext_wid |]) =
  mbMap2 ExtWidening_Mb mb_tp $
  mbSeparate (MNil :>: Proxy) $
  extMbExtWidening vars1 (CruCtxCons vars2 $ mbLift mb_tp) p $
  mbCombine mb_ext_wid

extExtWidening :: prx vars -> ValuePerm var -> ExtWidening args vars ->
                  ExtWidening args (vars :> var)
extExtWidening vars p ext_wid =
  elimEmptyMb $ extMbExtWidening vars CruCtxNil p $ emptyMb ext_wid

-- newtype MaybeVar a = MaybeVar { unMaybeVar :: Maybe (ExprVar a) }

data WideningState vars1 vars2 =
  WideningState { _wstPSubst1 :: PartialSubst vars1,
                  _wstPSubst2 :: PartialSubst vars2,
                  _wstMbPerms1 :: MbValuePerms vars1,
                  _wstMbPerms2 :: MbValuePerms vars2 }

makeLenses ''WideningState

emptyWideningState :: CruCtx vars1 -> CruCtx vars2 ->
                      MbValuePerms vars1 -> MbValuePerms vars2 ->
                      WideningState vars1 vars2
emptyWideningState vars1 vars2 perms1 perms2 =
  WideningState (emptyPSubst vars1) (emptyPSubst vars2) perms1 perms2

-- | A proof that a type argument equals one of two other type arguments
data TpMux tp1 tp2 tp where
  TpMux1 :: TpMux tp1 tp2 tp1
  TpMux2 :: TpMux tp1 tp2 tp2

-- | Return either 'wstPSubst1' or 'wstPSubst2' depending on the 'TpMux'
wstPSubst :: TpMux evars1 evars2 evars ->
             Lens' (WideningState evars1 evars2) (PartialSubst evars)
wstPSubst TpMux1 = wstPSubst1
wstPSubst TpMux2 = wstPSubst2

-- | Return either 'wstMbPerms1' or 'wstMbPerms2' depending on the 'TpMux'
wstMbPerms :: TpMux evars1 evars2 evars ->
              Lens' (WideningState evars1 evars2) (MbValuePerms evars)
wstMbPerms TpMux1 = wstMbPerms1
wstMbPerms TpMux2 = wstMbPerms2

newtype PolyContT r m a =
  PolyContT { runPolyContT :: forall x. (a -> m (r x)) -> m (r x) }

instance Functor (PolyContT r m) where
  fmap f m = m >>= return . f

instance Applicative (PolyContT r m) where
  pure = return
  (<*>) = ap

instance Monad (PolyContT r m) where
  return x = PolyContT $ \k -> k x
  (PolyContT m) >>= f =
    PolyContT $ \k -> m $ \a -> runPolyContT (f a) k

type WideningM args vars1 vars2 =
  StateT (WideningState vars1 vars2)
  (PolyContT (ExtWidening args) Maybe)

runWideningM :: CruCtx vars1 -> CruCtx vars2 ->
                MbValuePerms vars1 -> MbValuePerms vars2 ->
                WideningM args vars1 vars2 (ValuePerms args) ->
                Maybe (ExtWidening args RNil)
runWideningM vars1 vars2 perms1 perms2 m =
  flip runPolyContT (Just . flip ExtWidening_Base MNil . fst) $
  flip runStateT (emptyWideningState vars1 vars2 perms1 perms2) m

-- | Test if an input evar has been set to an output value
inputEVarIsSetM :: TpMux vars1 vars2 vars -> Member vars (a :: CrucibleType) ->
                   WideningM args vars1 vars2 Bool
inputEVarIsSetM mux evar =
  isJust <$> flip psubstLookup evar <$> view (wstPSubst mux) <$> get

-- | Apply the current partial substitution for one of the sets of input evars
-- to an expression
psubstEVarsM :: (NuMatching a, Substable PartialSubst a Maybe) =>
                TpMux vars1 vars2 vars -> Mb vars a ->
                WideningM args vars1 vars2 (Maybe a)
psubstEVarsM mux mb_a =
  partialSubst <$> (view (wstPSubst mux) <$> get) <*> return mb_a

-- | Apply the current partial substitution for one of the sets of input evars
-- to an expression in additional variables bindings, lifting that expression
-- out of those bindings if possible
psubstEVarsLiftM :: (NuMatching a, Substable PartialSubst a Maybe) =>
                    TpMux vars1 vars2 evars -> KnownCruCtx vars ->
                    Mb (evars :++: vars) a ->
                    WideningM args vars1 vars2 (Maybe a)
psubstEVarsLiftM mux vars mb_a =
  (view (wstPSubst mux) <$> get) >>= \psubst ->
  let psubst' = psubstAppend psubst $ emptyPSubst $ knownCtxToCruCtx vars in
  return $ partialSubst psubst' mb_a

-- | Set the substitution for an input evar, assuming it has not been set
setEVarM :: TpMux vars1 vars2 vars -> Member vars a -> PermExpr a ->
            WideningM args vars1 vars2 ()
setEVarM mux evar e = modify (over (wstPSubst mux) (psubstSet evar e))

-- | Get the permissions for an input evar
getEvarPermsM :: TpMux vars1 vars2 vars -> Member vars a ->
                 WideningM args vars1 vars2 (Mb vars (ValuePerm a))
getEvarPermsM mux evar =
  fmap (RL.get evar) <$> view (wstMbPerms mux) <$> get

-- | Bind a fresh evar in the output 'Widening' whose permissions are given by a
-- computation, and return that evar for future computations
--
-- FIXME: figure out a nicer way to write this?
bindWideningVar :: TypeRepr tp -> WideningM args vars1 vars2 (ValuePerm tp) ->
                   WideningM args vars1 vars2 (ExprVar tp)
bindWideningVar tp m =
  StateT $ \s -> PolyContT $ \k ->
  fmap (ExtWidening_Mb tp) $ mbMaybe $ nu $ \x ->
  runPolyContT (runStateT m s) $ \(p,s') ->
  fmap (extExtWidening Proxy p) $ k (x,s')
-}

----------------------------------------------------------------------
-- * Widening Itself
----------------------------------------------------------------------

widenExprs :: KnownCruCtx vars -> CruCtx tps ->
              Mb vars (RAssign PermExpr tps) ->
              Mb vars (RAssign PermExpr tps) ->
              WideningM (RAssign PermExpr tps)
widenExprs = error "FIXME HERE NOW"

widenPerm :: KnownCruCtx vars -> TypeRepr a ->
             Mb vars (ValuePerm a) -> Mb vars (ValuePerm a) ->
             WideningM (Mb vars (ValuePerm a))
widenPerm = error "FIXME HERE NOW"

-- | Widen a sequence of permissions
widenPerms :: KnownCruCtx vars -> CruCtx tps ->
              Mb vars (ValuePerms tps) -> Mb vars (ValuePerms tps) ->
              WideningM (Mb vars (ValuePerms tps))
widenPerms vars tps mb_ps1 mb_ps2 =
  widenPerms' vars tps (mbMatch mb_ps1) (mbMatch mb_ps2)

-- | The main worker for 'widenPerms'
--
-- FIXME HERE NOW: should we do permissions with determined vars first?
widenPerms' :: KnownCruCtx vars -> CruCtx tps ->
               MatchedMb vars (ValuePerms tps) ->
               MatchedMb vars (ValuePerms tps) ->
               WideningM (Mb vars (ValuePerms tps))
widenPerms' vars _ [nuMP| MNil |] _ = return $ nuMulti vars $ const MNil
widenPerms' vars (CruCtxCons tps tp) [nuMP| ps1 :>: p1 |] [nuMP| ps2 :>: p2 |] =
  mbMap2 (:>:) <$> widenPerms vars tps ps1 ps2 <*> widenPerm vars tp p1 p2


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
     widenExprs MNil args (emptyMb $ RL.map PExpr_Var args_ns1)
       (emptyMb $ RL.map PExpr_Var args_ns2)
     return ()
