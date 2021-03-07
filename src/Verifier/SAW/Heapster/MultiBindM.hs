{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE EmptyDataDecls #-}

module Verifier.SAW.Heapster.MultiBindM where

import Data.Kind
import Data.Functor.Compose
import Data.Functor.Product
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Trans.Cont (evalContT)

import Data.Parameterized.Some

import Data.Binding.Hobbits
import Data.Type.RList (RList(..), RAssign(..), (:++:), append, memberElem,
                        mapRAssign, mapToList)
import qualified Data.Type.RList as RL
import Data.Binding.Hobbits.Mb (mbMap2)
import Data.Binding.Hobbits.Closed
import Data.Binding.Hobbits.Liftable
import Data.Binding.Hobbits.MonadBind as MB
import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap
import Data.Binding.Hobbits.NameSet (NameSet, SomeName(..), toList)
import qualified Data.Binding.Hobbits.NameSet as NameSet
import Data.Binding.Hobbits.NuMatching
import Data.Binding.Hobbits.NuMatchingInstances

import Verifier.SAW.Heapster.CruUtil


mbSome :: Mb ctx (Some f) -> Some (Compose (Mb ctx) f)
mbSome = error "FIXME HERE NOW"

class GetProxies w where
  getProxies :: w ctx -> RAssign Proxy ctx

newtype BindStRet ctx w a ctx' =
  BindStRet { unBindStRet :: Mb ctx' (w (ctx :++: ctx'), a) }

mbBindStRetProxy :: Mb ctx1 (BindStRet ctx2 w a ctx3) -> Proxy ctx3
mbBindStRetProxy _ = Proxy

class CtxAssocProof (w :: RList k -> Type) where
  ctxAssocProof :: f1 ctx1 -> f2 ctx2 -> f3 ctx3 ->
                   w ((ctx1 :++: ctx2) :++: ctx3) ->
                   ((ctx1 :++: ctx2) :++: ctx3) :~: (ctx1 :++: (ctx2 :++: ctx3))

mbSomeBindStRet :: CtxAssocProof w => f1 ctx1 -> f2 ctx2 ->
                   Mb ctx2 (Some (BindStRet (ctx1 :++: ctx2) w a)) ->
                   Some (BindStRet ctx1 w a)
mbSomeBindStRet ctx1 ctx2 mb =
  case mbSome mb of
    Some (Compose mb_mb_ret)
      | ctx3 <- mbBindStRetProxy mb_mb_ret
      , mb_w_a <- mbCombine $ fmap unBindStRet mb_mb_ret
      , Refl <- mbLift $ fmap (ctxAssocProof ctx1 ctx2 ctx3 . fst) mb_w_a ->
        Some (BindStRet mb_w_a)

newtype BindStT (w :: RList k -> Type) m a =
  BindStT { unBindStT :: forall ctx. w ctx -> m (Some (BindStRet ctx w a)) }

instance (MonadStrongBind m, CtxAssocProof w) => Monad (BindStT w m) where
  return x = BindStT $ \w -> return $ Some $ BindStRet (emptyMb (w, x))
  m >>= f =
    BindStT $ \w1 ->
    do Some (BindStRet mb1) <- unBindStT m w1
       mbSomeBindStRet Proxy Proxy <$> strongMbM (fmap (\(w2, a) -> unBindStT (f a) w2) mb1)

instance (MonadStrongBind m, CtxAssocProof w) => Functor (BindStT w m) where
  fmap f xs = xs >>= return . f

instance (MonadStrongBind m, CtxAssocProof w) => Applicative (BindStT w m) where
  pure = return
  m1 <*> m2 = m1 >>= (\x1 -> m2 >>= (\x2 -> return (x1 x2)))


{-
-- newtype BindT2 m a = BindT2 { unBindT2 :: Some (Flip Mb (m a)) }
data BindT2 w m a = forall ctx. BindT2 (w ctx) (Mb ctx (m a))

someifyBindT2 :: BindT2 w m a -> Some (Product w (Flip Mb (m a)))
someifyBindT2 (BindT2 w mb_m) = Some (Pair w (Flip mb_m))

mbBindT2 :: BindMonoid w => w ctx -> Mb ctx (BindT2 m a) -> BindT2 w m a
mbBindT2 w1 mb_m =
  case mbSome (fmap somifyBindT2 mb_m) of
    Some (Compose mb_prod_flip) ->
      let mb_w2 = fmap (\(Pair w2 _) -> w2) mb_prod_flip
          mb_mb_m = fmap (\(Pair _ (Flip mb_m))) mb_prod_flip in
      BindT2 (bmappend w1 mb_w2) (mbCombine mb_mb_m)

instance (BindMonoid w, Monad m) => Monad (BindT2 m) where
  return x = BindT $ emptyMb $ return x
  (BindT2 w1 mb_m) >>= f =
    BindT $
    do Some (Pair w1 (Flip mb_a)) <- unBindT m
       Some (Compose mb_w2_mb_b) <-
         mbSome <$> strongMbM (fmap (unBindT . f) mb_a)
       let mb_w2 = fmap (\(Pair w2 _) -> w2) mb_w2_mb_b
       let mb_b = mbCombine $ fmap (\(Pair _ (Flip b)) -> b) mb_w2_mb_b
       return $ BindRet (bmappend w1 mb_w2) mb_b

instance (BindMonoid w, Monad m) => Functor (BindT2 w m) where
  fmap f xs = xs >>= return . f

instance (BindMonoid w, Monad m) => Applicative (BindT w m) where
  pure = return
  m1 <*> m2 = m1 >>= (\x1 -> m2 >>= (\x2 -> return (x1 x2)))
-}


newtype Flip f a b = Flip { unFlip :: f b a }

type BindRet w a = Some (Product w (Flip Mb a))

pattern BindRet w mb_a = Some (Pair w (Flip mb_a))

instance LiftableAny1 f => Liftable (Some f) where
  mbLift [nuP| Some x |] = Some $ mbLiftAny1 x

class BindMonoid (w :: RList k -> Type) where
  bmempty :: w RNil
  bmappend :: w ctx1 -> Mb ctx1 (w ctx2) -> w (ctx1 :++: ctx2)

newtype BindT (w :: RList k -> Type) m a =
  BindT { unBindT :: m (BindRet w a) }

instance (MonadStrongBind m, BindMonoid w) => Monad (BindT w m) where
  return x = BindT $ return $ BindRet bmempty (emptyMb x)
  m >>= f =
    BindT $
    do Some (Pair w1 (Flip mb_a)) <- unBindT m
       Some (Compose mb_w2_mb_b) <-
         mbSome <$> strongMbM (fmap (unBindT . f) mb_a)
       let mb_w2 = fmap (\(Pair w2 _) -> w2) mb_w2_mb_b
       let mb_b = mbCombine $ fmap (\(Pair _ (Flip b)) -> b) mb_w2_mb_b
       return $ BindRet (bmappend w1 mb_w2) mb_b

instance (MonadStrongBind m, BindMonoid w) => Functor (BindT w m) where
  fmap f xs = xs >>= return . f

instance (MonadStrongBind m, BindMonoid w) => Applicative (BindT w m) where
  pure = return
  m1 <*> m2 = m1 >>= (\x1 -> m2 >>= (\x2 -> return (x1 x2)))

data UnbindFun r (ctx :: RList k) =
  UnbindFun (RAssign Proxy ctx) (Mb ctx r -> r)

appUnbindFun :: UnbindFun r ctx -> Mb ctx r -> r
appUnbindFun (UnbindFun _ f) = f

unbindFunCtx :: UnbindFun r ctx -> RAssign Proxy ctx
unbindFunCtx (UnbindFun ctx _) = ctx

mbUnbindFunCtx :: Mb ctx' (UnbindFun r ctx) -> RAssign Proxy ctx
mbUnbindFunCtx = mbLift . fmap unbindFunCtx

instance BindMonoid (UnbindFun r) where
  bmempty = UnbindFun MNil elimEmptyMb
  bmappend f1 mb_f2 =
    UnbindFun
    (RL.append (unbindFunCtx f1) (mbUnbindFunCtx mb_f2))
    (appUnbindFun f1 . mbApply (fmap appUnbindFun mb_f2)
     . mbSeparate (mbUnbindFunCtx mb_f2))

data LCTag
type LCVar = Name LCTag
type LCBinding = Binding LCTag

data LC
  = LC_Var LCVar
  | LC_App LC LC
  | LC_Lam (LCBinding LC)
  | LC_Let LC (LCBinding LC)
  deriving (Show)

data LCModule
  = LCModNil
  | LCModCons String LC (LCBinding LCModule)


-- type LCBuilder = BindT (UnbindFun LCModule) (BindT (UnbindFun LC) Identity)


newtype UnMb (reg :: Type) a = UnMb { reMb :: a }

unMbCombine :: UnMb reg1 (UnMb reg2 a) -> UnMb (reg1,reg2) a
unMbCombine (UnMb (UnMb a)) = UnMb a

unMbSplit :: UnMb (reg1,reg2) a -> UnMb reg1 (UnMb reg2 a)
unMbSplit (UnMb a) = UnMb (UnMb a)

unMbSwap :: UnMb (reg1,reg2) a -> UnMb (reg2,reg1) a
unMbSwap (UnMb a) = UnMb a

unMbApply :: UnMb reg (a -> b) -> UnMb reg a -> UnMb reg b
unMbApply (UnMb f) (UnMb x) = UnMb (f x)

unMbClosed :: Closed a -> UnMb reg a
unMbClosed = UnMb . unClosed

applyWithUnMb :: (forall reg. Mb ctx (UnMb reg a -> (UnMb reg b, c))) ->
                 a -> (b, Mb ctx c)
applyWithUnMb f a = undefined
