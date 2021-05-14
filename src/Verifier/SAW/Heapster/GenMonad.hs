{-# Language BlockArguments #-}
{-# Language DeriveFunctor #-}
{-# Language FlexibleInstances, MultiParamTypeClasses #-} -- MonadState
{-# Language PolyKinds #-} -- gopenBinding
{-# Language TypeFamilies #-} -- Equality constraints
module Verifier.SAW.Heapster.GenMonad (
  -- * Core definitions
  GenStateCont(..), (>>>=), (>>>), liftGenStateContM,
  -- * Continuation operations
  gcaptureCC, gmapRet, gabortM, gparallel, gopenBinding,
  -- * State operations
  gmodify, withAltStateM, 
  ) where

import Data.Binding.Hobbits ( nuMultiWithElim1, Mb, Name, RAssign )
import Control.Monad.State ( ap, MonadState(get, put) )

-- | The generalized state-continuation monad
newtype GenStateCont s1 r1 s2 r2 a = GenStateCont {
  runGenStateCont :: s2 -> (s1 -> a -> r1) -> r2
  } deriving Functor

-- | Sequence two 'GenStateCont' values. Type-changing analogue of '>>='
(>>>=) :: GenStateCont s2 r2 s1 r1 a -> (a -> GenStateCont s3 r3 s2 r2 b) -> GenStateCont s3 r3 s1 r1 b
x >>>= y = GenStateCont \s1 z -> runGenStateCont x s1 \s2 a -> runGenStateCont (y a) s2 z

-- | Sequence two 'GenStateCont' values ignoring the return value. Type-changing analogue of '>>'
(>>>) :: GenStateCont s2 r2 s1 r1 a -> GenStateCont s3 r3 s2 r2 b -> GenStateCont s3 r3 s1 r1 b
m1 >>> m2 = m1 >>>= \_ -> m2

infixl 1 >>>=, >>>

-- NB. These instance must be specified as
-- instance (s1 ~ s2, r1 ~ r2) => Applicative (GenStateCont s1 r1 s2 r2) where
-- instead of
-- instance Applicative (GenStateCont s r s r) where
-- in order to ensure they are quickly selected by GHC even when it's not
-- immediately obvious that the types are equal.

instance (s1 ~ s2, r1 ~ r2) => Applicative (GenStateCont s1 r1 s2 r2) where
  pure x = GenStateCont \s k -> k s x
  (<*>) = ap

instance (s1 ~ s2, r1 ~ r2) => Monad (GenStateCont s1 r1 s2 r2) where
  (>>=) = (>>>=)

-- | Lift a monadic action into a generalized state-continuation monad
liftGenStateContM :: Monad m => m a -> GenStateCont s (m b) s (m b) a
liftGenStateContM m = GenStateCont \s k -> m >>= k s

-----------------------------------------------------------------------
-- Continuation operations
-----------------------------------------------------------------------

-- | Capture the current continuation while preserving the state.
gcaptureCC :: ((a -> r1) -> r2) -> GenStateCont s r1 s r2 a
gcaptureCC f = GenStateCont \s k -> f (k s)

-- | Run two generalized monad computations "in parallel" and combine their
-- results
gparallel ::
  (r1 -> r2 -> r3) ->
  GenStateCont s1 r s2 r1 a ->
  GenStateCont s1 r s2 r2 a ->
  GenStateCont s1 r s2 r3 a
gparallel f (GenStateCont m1) (GenStateCont m2) = GenStateCont \s k -> f (m1 s k) (m2 s k)

-- | Abort the current state-continuation computation and just return an @r2@
gabortM :: r2 -> GenStateCont s1 r1 s2 r2 a
gabortM ret = GenStateCont \_ _ -> ret

-----------------------------------------------------------------------
-- State operations
-----------------------------------------------------------------------

instance (s1 ~ s2, r1 ~ r2) => MonadState s1 (GenStateCont s1 r1 s2 r2) where
  get = GenStateCont \s k -> k s s
  put = gput

-- | Overwrite the previous state value (with the ability to change its type)
gput :: s -> GenStateCont s r s_ r ()
gput s = GenStateCont \_ k -> k s ()

-----------------------------------------------------------------------
-- Derived operations
-----------------------------------------------------------------------

-- | Apply a function to the state to update it.
gmodify :: (s -> t) -> GenStateCont t r s r ()
gmodify f = get >>>= gput . f

-- | Map a function over the final return value.
gmapRet :: (r1 -> r2) -> GenStateCont s r1 s r2 ()
gmapRet f_ret = gcaptureCC \k -> f_ret (k ())

-- | Name-binding in the generalized continuation monad (FIXME: explain)
gopenBinding ::
  (Mb ctx b1 -> r2) ->
  Mb ctx b2 ->
  GenStateCont s b1 s r2 (RAssign Name ctx, b2)
gopenBinding f_ret mb_a =
  gcaptureCC \k ->
  f_ret $ flip nuMultiWithElim1 mb_a $ \names a ->
  k (names, a)

-- | Run a generalized state computation with a different state type @s2@ inside
-- one with state type @s1@, using a lens-like pair of a getter function to
-- extract out the starting inner @s2@ state from the outer @s1@ state and an
-- update function to update the resulting outer @s1@ state with the final inner
-- @s2@ state.
withAltStateM ::
  (s4 -> s2) ->
  (s4 -> s1 -> s3) ->
  GenStateCont s1 r1 s2 r2 a ->
  GenStateCont s3 r1 s4 r2 a
withAltStateM s_get s_update m =
  get                  >>>= \s ->
  gput (s_get s)       >>>
  m                    >>>= \a ->
  gmodify (s_update s) >>>
  pure a
