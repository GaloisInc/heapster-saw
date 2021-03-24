{-# Language DeriveTraversable #-}
{-# Language TemplateHaskell #-}
{-# Options_GHC -Wno-unused-foralls #-}
module Verifier.SAW.Heapster.Located
  ( Located(..),
    Pos(..),
    HasPos(..),
  )where

import Data.Binding.Hobbits

data Located a = Located
  { locPos :: !Pos
  , locThing :: a
  }
  deriving (Functor, Foldable, Traversable, Show)

data Pos = Pos { posChar, posLine, posCol :: !Int }
  deriving Show

class HasPos a where
  pos :: a -> Pos

instance HasPos (Located a) where
  pos = locPos

instance HasPos Pos where
  pos = id

mkNuMatching [t| Pos |]
