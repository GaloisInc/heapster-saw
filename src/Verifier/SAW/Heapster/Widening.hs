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

import Data.Parameterized.Some
import Control.Monad.State
-- import Control.Monad.Cont

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits

import Lang.Crucible.Types


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
  WideningState { wstPSubst1 :: PartialSubst vars1,
                  wstPSubst2 :: PartialSubst vars2,
                  wstMbPerms1 :: MbValuePerms vars1,
                  wstMbPerms2 :: MbValuePerms vars2 }

emptyWideningState :: CruCtx vars1 -> CruCtx vars2 ->
                      MbValuePerms vars1 -> MbValuePerms vars2 ->
                      WideningState vars1 vars2
emptyWideningState vars1 vars2 perms1 perms2 =
  WideningState (emptyPSubst vars1) (emptyPSubst vars2) perms1 perms2

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


----------------------------------------------------------------------
-- * Widening Itself
----------------------------------------------------------------------

{-
class WideningUnify a where
  wideningUnify' :: MatchedMb vars1 a -> MatchedMb vars2 a ->
                    WideningM args vars1 vars2 a

wideningUnify :: WideningEq a => Mb vars1 a -> Mb vars2 a ->
                 WideningM args vars1 vars2 a
wideningUnify mb1 mb2 = wideningUnify (mbMatch mb1) (mbMatch mb2)

instance WideningUnify (PermExpr a) where
  wideningUnify' = error "FIXME HERE NOW"
-}

class WidenM a where
  widenM' :: MatchedMb vars1 a -> PartialSubst vars1 ->
             MatchedMb vars2 a -> PartialSubst vars2 ->
             WideningM args vars1 vars2 a

widenM :: WidenM a => Mb vars1 a -> Mb vars2 a ->
          WideningM args vars1 vars2 a
widenM mb1 mb2 =
  get >>= \st ->
  widenM' (mbMatch mb1) (wstPSubst1 st) (mbMatch mb2) (wstPSubst2 st)

instance WidenM (ValuePerm a) where
  widenM' = error "FIXME HERE NOW"
  {-
  widenM' [nuMP| ValPerm_Eq mb_e1 |] [nuMP| ValPerm_Eq mb_e2 |] =
    FIXME HERE NOW: do we just unify the two sides? Or maybe we have a way
                       to lift exprs out of their bindings by binding fresh vars? -}

-- FIXME HERE NOW: should we do permissions with determined vars first?
instance WidenM (ValuePerms ps) where
  widenM' [nuMP| MNil |] _ _ _ = return MNil
  widenM' [nuMP| ps1 :>: p1 |] _ [nuMP| ps2 :>: p2 |] _ =
    (:>:) <$> widenM ps1 ps2 <*> widenM p1 p2


----------------------------------------------------------------------
-- * Top-Level Entrypoints
----------------------------------------------------------------------

data Widening args vars =
  Widening { wideningVars :: CruCtx vars,
             wideningPerms :: MbValuePerms (args :++: vars) }

$(mkNuMatching [t| forall args vars. Widening args vars |])

completeMbExtWidening :: CruCtx vars ->
                         Mb (args :++: vars) (ExtWidening args vars) ->
                         Some (Widening args)
completeMbExtWidening vars (mbMatch -> [nuMP| ExtWidening_Base arg_ps ps |]) =
  Some $ Widening vars $ mbMap2 RL.append arg_ps ps
completeMbExtWidening vars (mbMatch ->
                            [nuMP| ExtWidening_Mb var mb_ext_wid |]) =
  completeMbExtWidening (CruCtxCons vars (mbLift var)) (mbCombine mb_ext_wid)

completeExtWidening :: Mb args (ExtWidening args RNil) -> Some (Widening args)
completeExtWidening = completeMbExtWidening CruCtxNil

-- | Top-level entrypoint
widen :: CruCtx args -> CruCtx vars1 -> CruCtx vars2 ->
         MbValuePerms (args :++: vars1) ->
         MbValuePerms (args :++: vars2) ->
         Maybe (Some (Widening args))
widen args vars1 vars2 mb_perms_args1_vars1 mb_perms_args2_vars2 =
  let prxs1 = cruCtxProxies vars1
      prxs2 = cruCtxProxies vars2 in
  fmap completeExtWidening $ mbMaybe $
  mbMap2 (\perms_args1_vars1 perms_args2_vars2 ->
           let perms_args1 = fmap (fst . RL.split args prxs1) perms_args1_vars1
               perms_vars1 = fmap (snd . RL.split args prxs1) perms_args1_vars1
               perms_args2 = fmap (fst . RL.split args prxs2) perms_args2_vars2
               perms_vars2 = fmap (snd . RL.split args prxs2) perms_args2_vars2 in
           runWideningM vars1 vars2 perms_vars1 perms_vars2 $
           widenM perms_args1 perms_args2)
  (mbSeparate prxs1 mb_perms_args1_vars1)
  (mbSeparate prxs2 mb_perms_args2_vars2)
