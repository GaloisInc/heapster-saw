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


-- FIXME HERE NOW: remove this test code

mbSome :: Mb ctx (Some f) -> Some (Compose (Mb ctx) f)
mbSome = error "FIXME HERE NOW"

newtype Flip f a b = Flip { unFlip :: f b a }

type BindRet w a = Some (Product w (Flip Mb a))

pattern BindRet w mb_a = Some (Pair w (Flip mb_a))

instance LiftableAny1 f => Liftable (Some f) where
  mbLift [nuP| Some x |] = Some $ mbLiftAny1 x

newtype BindT (w :: RList k -> Type) m a =
  BindT { unBindT :: m (BindRet w a) }

class BindMonoid (w :: RList k -> Type) where
  bmempty :: w RNil
  bmappend :: w ctx1 -> Mb ctx1 (w ctx2) -> w (ctx1 :++: ctx2)

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


type LCBuilder = BindT (UnbindFun LCModule) (BindT (UnbindFun LC) Identity)
