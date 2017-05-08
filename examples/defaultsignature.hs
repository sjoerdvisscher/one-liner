{-# LANGUAGE
    TypeOperators
  , DeriveGeneric
  , DeriveAnyClass
  , ConstraintKinds
  , FlexibleContexts
  , TypeApplications
  , DefaultSignatures
  #-}

import GHC.Generics
import Generics.OneLiner

import Data.Monoid


class Size t where

  size :: t -> Int

  default size :: (ADT t, Constraints t Size) => t -> Int
  size = succ . getSum . gfoldMap @Size (Sum . size)

instance Size Bool
instance Size a => Size (Maybe a)


class EnumAll t where

  enumAll :: [t]

  default enumAll :: (ADT t, Constraints t EnumAll) => [t]
  enumAll = createA @EnumAll enumAll

instance EnumAll Bool
instance EnumAll a => EnumAll (Maybe a)


infixr 5 :^:
data Tree a = Leaf { value :: a } | Tree a :^: Tree a
  deriving (Show, Generic, Size, EnumAll)

trees :: [Tree (Maybe Bool)]
trees = enumAll

sizes :: [Int]
sizes = map size trees
