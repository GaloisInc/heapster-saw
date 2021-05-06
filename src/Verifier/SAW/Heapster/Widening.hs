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

-- | Apply a partial substitution for the top-level evars to an expression in a
-- binding for both top-level and local evars
psubstTopEVars :: Substable PartialSubst a Maybe =>
                  PartialSubst evars -> KnownCruCtx vars ->
                  Mb (evars :++: vars) a -> Maybe (Mb vars a)
psubstTopEVars = error "FIXME HERE NOW"

-- | FIXME HERE NOW: documentation
widenPerm :: KnownCruCtx vars -> TypeRepr a ->
             Mb (vars1 :++: vars) (ValuePerm a) ->
             Mb (vars2 :++: vars) (ValuePerm a) ->
             WideningM args vars1 vars2 (Mb vars (ValuePerm a))
widenPerm vars tp mb_e1 mb_e2 =
  widenPerm' vars tp (mbMatch mb_e1) (mbMatch mb_e2)

-- | FIXME HERE NOW: documentation
widenPerm' :: KnownCruCtx vars -> TypeRepr a ->
              MatchedMb (vars1 :++: vars) (ValuePerm a) ->
              MatchedMb (vars2 :++: vars) (ValuePerm a) ->
              WideningM args vars1 vars2 (Mb vars (ValuePerm a))

-- If both sides are of the form eq(x &+ off) for top-level evars x
widenPerm' vars tp [nuMP| ValPerm_Eq mb_e1 |] [nuMP| ValPerm_Eq mb_e2 |]
  | Just (evar1, mb_off1) <- asMbTopEVarOffset vars mb_e1
  , Just (evar2, mb_off2) <- asMbTopEVarOffset vars mb_e2 =
    get >>= \st ->
    let psubst1 = wstPSubst1 st
        psubst2 = wstPSubst2 st in
    case (psubstLookup psubst1 evar1, psubstLookup psubst2 evar2) of
      -- If both top-level evars already have values, and e1 == e2, return e1
      (Just _, Just _)
        | Just mb_e1' <- psubstTopEVars psubst1 vars mb_e1
        , Just mb_e2' <- psubstTopEVars psubst2 vars mb_e2
        , mb_e1' == mb_e2' ->
          return $ fmap ValPerm_Eq mb_e1'

      -- If neither var is set, make a new variable, whose permissions are given
      -- by widening the permissions of x1 and x2 against each other
      (Nothing, Nothing)
        | vars_psubst <- emptyPSubst (knownCtxToCruCtx vars)
        , Just off1 <- partialSubst (psubstAppend psubst1 vars_psubst) mb_off1
        , Just off2 <- partialSubst (psubstAppend psubst2 vars_psubst) mb_off2 ->
          do let p1 = fmap (offsetPerm off1 . RL.get evar1) (wstMbPerms1 st)
                 p2 = fmap (offsetPerm off2 . RL.get evar2) (wstMbPerms2 st)
             n <- bindWideningVar tp $ fmap elimEmptyMb $ widenPerm MNil tp p1 p2
             put (st { wstPSubst1 =
                         psubstSet evar1 (offsetExpr (negatePermOffset off1) $
                                          PExpr_Var n) psubst1
                     , wstPSubst2 =
                         psubstSet evar2 (offsetExpr (negatePermOffset off2) $
                                          PExpr_Var n) psubst2 })
             return $ nuMulti vars $ const $ ValPerm_Eq $ PExpr_Var n


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
           fmap elimEmptyMb $ widenPerms MNil args perms_args1 perms_args2)
  (mbSeparate prxs1 mb_perms_args1_vars1)
  (mbSeparate prxs2 mb_perms_args2_vars2)
