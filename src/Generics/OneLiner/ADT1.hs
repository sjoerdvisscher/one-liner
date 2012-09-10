-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner.ADT1
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
  , TypeOperators
  , ConstraintKinds
  , ScopedTypeVariables
  #-}
module Generics.OneLiner.ADT1 where

import Generics.OneLiner.Info

import GHC.Prim (Constraint)
import Control.Applicative
import Data.Functor.Identity
import Data.Functor.Constant
import Data.Monoid


type f :~> g = forall x. f x -> g x

data FieldInfo t s = FieldInfo
  { fieldName :: String
  , project   :: t :~> s
  }

data For (c :: (* -> *) -> Constraint) = For

class ADT1 t where

  ctorInfo :: t a -> CtorInfo

  type Constraints t c :: Constraint
  buildsA :: (Constraints t c, Applicative f)
           => For c
           -> ((forall a. t a -> a) -> f b)
           -> (forall s. c s => FieldInfo t s -> f (s b))
           -> [f (t b)]

builds :: (ADT1 t, Constraints t c) 
       => For c
       -> ((forall a. t a -> a) -> b)
       -> (forall s. c s => FieldInfo t s -> s b)
       -> [t b]
builds for f g = fmap runIdentity $ buildsA for (Identity . f) (Identity . g)

mbuilds :: forall t c m. (ADT1 t, Constraints t c, Monoid m) 
        => For c
        -> ((forall a. t a -> a) -> m)
        -> (forall s. c s => FieldInfo t s -> m)
        -> [m]
mbuilds for f g = fmap getConstant ms
  where
    ms :: [Constant m (t b)]
    ms = buildsA for (Constant . f) (Constant . g)

(!) :: t a -> FieldInfo t s -> s a
t ! FieldInfo _ proj = proj t

at :: ADT1 t => [a] -> t b -> a
at as t = as !! ctorIndex (ctorInfo t)