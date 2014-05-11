-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner.ADT
-- Copyright   :  (c) Sjoerd Visscher 2012
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module is for writing generic functions on algebraic data types 
-- of kind @*@. These data types must be an instance of the `ADT` type class.
-- 
-- Here's an example how to write such an instance for this data type:
--
-- @
-- data T a = A Int a | B a (T a)
-- @
--
-- @
-- instance `ADT` (T a) where
--   `ctorIndex` A{} = 0
--   `ctorIndex` B{} = 1
--   `ctorInfo` _ 0 = `ctor` \"A\"
--   `ctorInfo` _ 1 = `ctor` \"B\"
--   type `Constraints` (T a) c = (c Int, c a, c (T a))
--   `buildsRecA` `For` sub rec = 
--     [ A `<$>` sub (`FieldInfo` (\\(A i _) -> i)) `<*>` sub (`FieldInfo` (\\(A _ a) -> a))
--     , B `<$>` sub (`FieldInfo` (\\(B a _) -> a)) `<*>` rec (`FieldInfo` (\\(B _ t) -> t))
--     ]
-- @
--
-- And this is how you would write generic equality, using the `All` monoid:
--
-- @
-- eqADT :: (`ADT` t, `Constraints` t `Eq`) => t -> t -> `Bool`
-- eqADT s t = `ctorIndex` s == `ctorIndex` t `&&` 
--   `getAll` (`mbuilds` (`For` :: `For` `Eq`) (\\fld -> `All` $ s `!` fld `==` t `!` fld) \``at`\` s)
-- @
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
  , ADTRecord(..)
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

    -- ** ...for single constructor data types
  , build
  , op0
  , op1
  , op2
  
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
  
  -- | @ctorInfo n@ gives constructor information, f.e. its name, for the @n@th constructor.
  --   The first argument is a dummy argument and can be @(undefined :: t)@.
  ctorInfo :: t -> Int -> CtorInfo

  -- | The constraints needed to run `buildsA` and `buildsRecA`. 
  -- It should be a list of all the types of the subcomponents of @t@, each applied to @c@.
  type Constraints t c :: Constraint
  
  buildsA :: (Constraints t c, Applicative f)
          => For c -- ^ Witness for the constraint @c@.
          -> (forall s. c s => FieldInfo (t -> s) -> f s) -- ^ This function should return a value
             -- for each subcomponent of @t@, wrapped in an applicative functor @f@. It is given 
             -- information about the field, which contains a projector function to get the subcomponent 
             -- from a value of type @t@. The type of the subcomponent is an instance of class @c@.
          -> [f t] -- ^ A list of results, one for each constructor of type @t@. Each element is the 
             -- result of applicatively applying the constructor to the results of the given function 
             -- for each field of the constructor.
  
  default buildsA :: (c t, Constraints t c, Applicative f) 
                  => For c -> (forall s. c s => FieldInfo (t -> s) -> f s) -> [f t]
  buildsA for f = buildsRecA for f f
  
  buildsRecA :: (Constraints t c, Applicative f) 
             => For c -- ^ Witness for the constraint @c@.
             -> (forall s. c s => FieldInfo (t -> s) -> f s) -- ^ This function should return a value
                -- for each subcomponent of @t@, wrapped in an applicative functor @f@. It is given 
                -- information about the field, which contains a projector function to get the subcomponent 
                -- from a value of type @t@. The type of the subcomponent is an instance of class @c@.
             -> (FieldInfo (t -> t) -> f t) -- ^ This function should return a value
                -- for each subcomponent of @t@ that is itself of type @t@.
             -> [f t] -- ^ A list of results, one for each constructor of type @t@. Each element is the 
             -- result of applicatively applying the constructor to the results of the given function 
             -- for each field of the constructor.
  buildsRecA for sub _ = buildsA for sub

-- | Add an instance for this class if the data type has exactly one constructor.
--
--   This class has no methods.
class ADT t => ADTRecord t where

-- | `buildsA` specialized to the `Identity` applicative functor.
builds :: (ADT t, Constraints t c) 
       => For c -> (forall s. c s => FieldInfo (t -> s) -> s) -> [t]
builds for f = runIdentity <$> buildsA for (Identity . f)  

-- | `buildsA` specialized to the `Constant` applicative functor, which collects monoid values @m@.
mbuilds :: forall t c m. (ADT t, Constraints t c, Monoid m) 
        => For c -> (forall s. c s => FieldInfo (t -> s) -> m) -> [m]
mbuilds for f = getConstant <$> (buildsA for (Constant . f) :: [Constant m t])

-- | Transform a value by transforming each subcomponent.
gmap :: (ADT t, Constraints t c)
     => For c -> (forall s. c s => s -> s) -> t -> t
gmap for f t = builds for (\fld -> f (t ! fld)) `at` t

-- | Fold a value, by mapping each subcomponent to a monoid value and collecting those. 
gfoldMap :: (ADT t, Constraints t c, Monoid m)
         => For c -> (forall s. c s => s -> m) -> t -> m
gfoldMap for f = getConstant . gtraverse for (Constant . f)

-- | Applicative traversal given a way to traverse each subcomponent.
gtraverse :: (ADT t, Constraints t c, Applicative f) 
          => For c -> (forall s. c s => s -> f s) -> t -> f t
gtraverse for f t = buildsA for (\fld -> f (t ! fld)) `at` t

-- | `builds` for data types with exactly one constructor
build :: (ADTRecord t, Constraints t c) 
      => For c -> (forall s. c s => FieldInfo (t -> s) -> s) -> t
build for f = head $ builds for f

-- | Derive a 0-ary operation by applying the operation to every subcomponent.
op0 :: (ADTRecord t, Constraints t c) => For c -> (forall s. c s => s) -> t
op0 for op = build for (const op)

-- | Derive a unary operation by applying the operation to every subcomponent.
op1 :: (ADTRecord t, Constraints t c) => For c -> (forall s. c s => s -> s) -> t -> t
op1 for op t = build for (\fld -> op $ t ! fld)

-- | Derive a binary operation by applying the operation to every subcomponent.
op2 :: (ADTRecord t, Constraints t c) => For c -> (forall s. c s => s -> s -> s) -> t -> t -> t
op2 for op s t = build for (\fld -> (s ! fld) `op` (t ! fld))




infixl 9 !
-- | Get the subcomponent by using the projector from the field information.
(!) :: t -> FieldInfo (t -> s) -> s
t ! fld = project fld t

-- | Get the value from the result of one of the @builds@ functions that matches the constructor of @t@.
at :: ADT t => [a] -> t -> a
at as t = as !! ctorIndex t



instance ADT () where
  
  type Constraints () c = ()
  ctorInfo _ 0 = ctor "()"
  buildsA For _ = [ pure () ]

instance ADTRecord () where
  
instance ADT (a, b) where
  
  type Constraints (a, b) c = (c a, c b)
  ctorInfo _ 0 = ctor "(,)"
  buildsA For f = [ (,) <$> f (FieldInfo fst) <*> f (FieldInfo snd) ]

instance ADTRecord (a, b) where

instance ADT (a, b, c) where

  type Constraints (a, b, c) tc = (tc a, tc b, tc c)
  ctorInfo _ 0 = ctor "(,,)"
  buildsA For f = [(,,) <$> f (FieldInfo (\(a, _, _) -> a))
                        <*> f (FieldInfo (\(_, b, _) -> b))
                        <*> f (FieldInfo (\(_, _, c) -> c))
                  ]

instance ADTRecord (a, b, c) where

instance ADT (a, b, c, d) where

  type Constraints (a, b, c, d) tc = (tc a, tc b, tc c, tc d)
  ctorInfo _ 0 = ctor "(,,,)"
  buildsA For f = [(,,,) <$> f (FieldInfo (\(a, _, _, _) -> a))
                         <*> f (FieldInfo (\(_, b, _, _) -> b))
                         <*> f (FieldInfo (\(_, _, c, _) -> c))
                         <*> f (FieldInfo (\(_, _, _, d) -> d))
                  ]

instance ADTRecord (a, b, c, d) where

instance ADT Bool where

  ctorIndex False = 0
  ctorIndex True  = 1
  ctorInfo _ 0 = ctor "False"
  ctorInfo _ 1 = ctor "True"

  type Constraints Bool c = ()
  buildsA For _ = [ pure False, pure True ]

instance ADT (Either a b) where

  ctorIndex Left{}  = 0
  ctorIndex Right{} = 1
  ctorInfo _ 0 = ctor "Left"
  ctorInfo _ 1 = ctor "Right"

  type Constraints (Either a b) c = (c a, c b)
  buildsA For f = 
    [ Left  <$> f (FieldInfo (\(Left a)  -> a))
    , Right <$> f (FieldInfo (\(Right a) -> a))
    ]
    
instance ADT (Maybe a) where

  ctorIndex Nothing = 0
  ctorIndex Just{}  = 1
  ctorInfo _ 0 = ctor "Nothing"
  ctorInfo _ 1 = ctor "Just"

  type Constraints (Maybe a) c = c a
  buildsA For f = 
    [ pure Nothing
    , Just <$> f (FieldInfo fromJust)
    ]

instance ADT [a] where

  ctorIndex []    = 0
  ctorIndex (_:_) = 1
  ctorInfo _ 0 = ctor "[]"
  ctorInfo _ 1 = CtorInfo ":" False (Infix RightAssociative 5)

  type Constraints [a] c = (c a, c [a])
  buildsRecA For sub rec = 
    [ pure []
    , (:) <$> sub (FieldInfo head) <*> rec (FieldInfo tail)]
  