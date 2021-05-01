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
import Control.Monad.Cont

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits

import Lang.Crucible.Types

data Widening args vars =
  Widening { wideningVars :: CruCtx vars,
             wideningPerms :: MbValuePerms (args :++: vars) }

$(mkNuMatching [t| forall args vars. Widening args vars |])

{-
mbWidening :: TypeRepr var -> Mb var (Widening args vars) ->
              Widening args ((RNil :> var) :++: vars)
mbWidening tp [nuP| Widening vars mb_perms |] =
  Widening (appendCruCtx (singletonCruCtx tp) (mbLift vars))
  (mbCombine )
-}

{-
-- | A computation type for binding fresh names
data FreshM a
  = PureFreshM a
  | forall tp. MbFreshM (TypeRepr tp) (Mb tp (FreshM a))

-- NOTE: we shouldn't need this instance...
instance Functor FreshM where
  fmap f (PureFreshM a) = PureFreshM $ f a
  fmap f (MbFreshM tp mb_m) =
    MbFreshM tp $ fmap (fmap f) mb_m
-}

-- | A 'Widening' for some list of variables that extends @vars@
data ExtWidening args vars
  = ExtWidening_Base (ValuePerms (args :++: vars))
  | forall var. ExtWidening_Mb (TypeRepr var) (Binding var
                                               (ExtWidening args (vars :> var)))

$(mkNuMatching [t| forall args vars. ExtWidening args vars |])

completeMbExtWidening :: CruCtx vars ->
                         Mb (args :++: vars) (ExtWidening args vars) ->
                         Some (Widening args)
completeMbExtWidening vars (mbMatch -> [nuMP| ExtWidening_Base perms |]) =
  Some $ Widening vars perms
completeMbExtWidening vars (mbMatch ->
                            [nuMP| ExtWidening_Mb var mb_ext_wid |]) =
  completeMbExtWidening (CruCtxCons vars (mbLift var)) (mbCombine mb_ext_wid)

completeExtWidening :: Mb args (ExtWidening args RNil) -> Some (Widening args)
completeExtWidening = completeMbExtWidening CruCtxNil

newtype MaybeVar a = MaybeVar { unMaybeVar :: Maybe (ExprVar a) }

data WideningState vars1 vars2 =
  WideningState (RAssign MaybeVar vars1) (RAssign MaybeVar vars2)
  (MbValuePerms vars1) (MbValuePerms vars2)

emptyWideningState :: CruCtx vars1 -> CruCtx vars2 ->
                      MbValuePerms vars1 -> MbValuePerms vars2 ->
                      WideningState vars1 vars2
emptyWideningState vars1 vars2 perms1 perms2 =
  WideningState
  (RL.map (const $ MaybeVar Nothing) $ cruCtxProxies vars1)
  (RL.map (const $ MaybeVar Nothing) $ cruCtxProxies vars2)
  perms1 perms2

type WideningM args vars1 vars2 =
  StateT (WideningState vars1 vars2)
  (ContT (ExtWidening args RNil) Maybe)

runWideningM :: CruCtx vars1 -> CruCtx vars2 ->
                MbValuePerms vars1 -> MbValuePerms vars2 ->
                WideningM args vars1 vars2 (ValuePerms args) ->
                Maybe (ExtWidening args RNil)
runWideningM vars1 vars2 perms1 perms2 m =
  flip runContT (Just . ExtWidening_Base . fst) $
  flip runStateT (emptyWideningState vars1 vars2 perms1 perms2) m

widenPerm :: Mb vars1 (ValuePerm a) -> Mb vars2 (ValuePerm a) ->
             WideningM args vars1 vars2 (ValuePerm a)
widenPerm = error "FIXME HERE NOW"

widenPerms :: Mb vars1 (ValuePerms ps) -> Mb vars2 (ValuePerms ps) ->
              WideningM args vars1 vars2 (ValuePerms ps)
widenPerms (mbMatch -> [nuMP| MNil |]) _ = return MNil
widenPerms (mbMatch -> [nuMP| ps1 :>: p1 |])
  (mbMatch -> [nuMP| ps2 :>: p2 |]) =
  (:>:) <$> widenPerms ps1 ps2 <*> widenPerm p1 p2

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
           widenPerms perms_args1 perms_args2)
  (mbSeparate prxs1 mb_perms_args1_vars1)
  (mbSeparate prxs2 mb_perms_args2_vars2)
