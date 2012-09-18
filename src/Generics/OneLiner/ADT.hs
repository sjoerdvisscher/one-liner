-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner.ADT
-- Copyright   :  (c) Sjoerd Visscher 2012
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
{-# LANGUAGE 
    RankNTypes
  , TypeFamilies
  , ConstraintKinds
  , FlexibleInstances
  , DefaultSignatures
  , ScopedTypeVariables
  #-}
module Generics.OneLiner.ADT (
  
    -- * Re-exports
    module Generics.OneLiner.Info
  , Constraint
    -- | The kind of constraints
    
    -- * The @ADT@ type class
  , ADT(..)
  , For(..)

    -- * Helper functions
  , (!)
  , at
  
    -- * Derived traversal schemes
  , builds
  , mbuilds
  , gmap
  , gfoldMap
  , gtraverse
  
  ) where
  
import Generics.OneLiner.Info

import GHC.Prim (Constraint)
import Control.Applicative
import Data.Functor.Identity
import Data.Functor.Constant
import Data.Monoid

import Data.Maybe (fromJust)


-- | Tell the compiler which class we want to use in the traversal. Should be used like this:
--
-- > (For :: For Show)
--
-- Where @Show@ can be any class.
data For (c :: * -> Constraint) = For

-- | Type class for algebraic data types of kind @*@. Minimal implementation: `ctorIndex` and either `buildsA`
-- if the type @t@ is not recursive, or `buildsRecA` if the type @t@ is recursive.
class ADT t where

  -- | Gives the index of the constructor of the given value in the list returned by `buildsA` and `buildsRecA`.
  ctorIndex :: t -> Int
  ctorIndex _ = 0

  -- | The constraints needed to run `buildsA` and `buildsRecA`. 
  -- It should be a list of all the types of the subcomponents of @t@, each applied to @c@.
  -- For example, if you have a data type like:
  --
  -- > data T a = A Int a | B a (T a)
  --
  -- Then the constaints should be
  --
  -- > type Constraints (T a) c = (c Int, c a, c (T a))
  type Constraints t c :: Constraint
  
  buildsA :: (Constraints t c, Applicative f)
          => For c -- ^ Witness for the constraint @c@.
          -> (forall s. c s => FieldInfo (t -> s) -> f s) -- ^ This function should return a value
             -- for each subcomponent of @t@, wrapped in an applicative functor @f@. It is given 
             -- information about the field, which contains a projector function to get the subcomponent 
             -- from a value of type @t@. The type of the subcomponent is an instance of class @c@.
          -> [(CtorInfo, f t)] -- ^ A list of pairs, one for each constructor of type @t@. Each pair
             -- consists of information about the constructor and the result of applicatively applying 
             -- the constructor to the results of the given function for each field of the constructor.
  
  default buildsA :: (c t, Constraints t c, Applicative f) 
                  => For c -> (forall s. c s => FieldInfo (t -> s) -> f s) -> [(CtorInfo, f t)]  
  buildsA for f = buildsRecA for f f
  
  buildsRecA :: (Constraints t c, Applicative f) 
             => For c -- ^ Witness for the constraint @c@.
             -> (forall s. c s => FieldInfo (t -> s) -> f s) -- ^ This function should return a value
                -- for each subcomponent of @t@, wrapped in an applicative functor @f@. It is given 
                -- information about the field, which contains a projector function to get the subcomponent 
                -- from a value of type @t@. The type of the subcomponent is an instance of class @c@.
             -> (FieldInfo (t -> t) -> f t) -- ^ This function should return a value
                -- for each subcomponent of @t@ that is itself of type @t@.
             -> [(CtorInfo, f t)] -- ^ A list of pairs, one for each constructor of type @t@. Each pair
                -- consists of information about the constructor and the result of applicatively applying 
                -- the constructor to the results of the given functions for each field of the constructor.
  buildsRecA for sub _ = buildsA for sub

-- | `buildsA` specialized to the `Identity` applicative functor.
builds :: (ADT t, Constraints t c) 
       => For c -> (forall s. c s => FieldInfo (t -> s) -> s) -> [(CtorInfo, t)]
builds for f = fmap runIdentity <$> buildsA for (Identity . f)  

-- | `buildsA` specialized to the `Constant` applicative functor, which collects monoid values @m@.
mbuilds :: forall t c m. (ADT t, Constraints t c, Monoid m) 
        => For c -> (forall s. c s => FieldInfo (t -> s) -> m) -> [(CtorInfo, m)]
mbuilds for f = fmap getConstant <$> ms
  where
    ms :: [(CtorInfo, Constant m t)]
    ms = buildsA for (Constant . f)

-- | Transform a value by transforming each subcomponent.
gmap :: (ADT t, Constraints t c)
     => For c -> (forall s. c s => s -> s) -> t -> t
gmap for f t = builds for (\info -> f (t ! info)) `at` t

-- | Fold a value, by mapping each subcomponent to a monoid value and collecting those. 
gfoldMap :: (ADT t, Constraints t c, Monoid m)
         => For c -> (forall s. c s => s -> m) -> t -> m
gfoldMap for f = getConstant . gtraverse for (Constant . f)

-- | Applicative traversal given a way to traverse each subcomponent.
gtraverse :: (ADT t, Constraints t c, Applicative f) 
          => For c -> (forall s. c s => s -> f s) -> t -> f t
gtraverse for f t = buildsA for (\info -> f (t ! info)) `at` t


infixl 9 !
-- | Get the subcomponent by using the projector from the field information.
(!) :: t -> FieldInfo (t -> s) -> s
t ! info = project info t

-- | Get the value from the result of one of the @builds@ functions that matches the constructor of @t@.
at :: ADT t => [(a, b)] -> t -> b
at ab t = snd (ab !! ctorIndex t)



instance ADT () where
  
  type Constraints () c = ()
  buildsA For _ = [ (ctor "()", pure ()) ]
  
instance ADT Bool where

  ctorIndex False = 0
  ctorIndex True  = 1

  type Constraints Bool c = ()
  buildsA For _ = 
    [ (ctor "False", pure False)
    , (ctor "True",  pure True) ]

instance ADT (Either a b) where

  ctorIndex Left{}  = 0
  ctorIndex Right{} = 1

  type Constraints (Either a b) c = (c a, c b)
  buildsA For f = 
    [ (ctor "Left",  Left  <$> f (FieldInfo (\(Left a)  -> a)))
    , (ctor "Right", Right <$> f (FieldInfo (\(Right a) -> a)))
    ]

instance ADT (Maybe a) where

  ctorIndex Nothing = 0
  ctorIndex Just{}  = 1

  type Constraints (Maybe a) c = c a
  buildsA For f = 
    [ (ctor "Nothing", pure Nothing)
    , (ctor "Just", Just <$> f (FieldInfo fromJust))
    ]

instance ADT [a] where

  ctorIndex []    = 0
  ctorIndex (_:_) = 1

  type Constraints [a] c = (c a, c [a])
  buildsRecA For sub rec = 
    [ (ctor "[]", pure [])
    , (CtorInfo ":" False (Infix RightAssociative 5)
      ,(:) <$> sub (FieldInfo head) <*> rec (FieldInfo tail))]
  