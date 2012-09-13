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
module Generics.OneLiner.ADT where
  
import Generics.OneLiner.Info

import GHC.Prim (Constraint)
import Control.Applicative
import Data.Functor.Identity
import Data.Functor.Constant
import Data.Monoid

import Data.Maybe (fromJust)


data For (c :: * -> Constraint) = For

class ADT t where

  ctorIndex :: t -> Int
  ctorIndex _ = 0

  type Constraints t c :: Constraint
  buildsA :: (Constraints t c, Applicative f) 
          => For c -> (forall s. c s => FieldInfo (t -> s) -> f s) -> [(CtorInfo, f t)]
  
  default buildsA :: (c t, Constraints t c, Applicative f) 
                  => For c -> (forall s. c s => FieldInfo (t -> s) -> f s) -> [(CtorInfo, f t)]  
  buildsA for f = buildsRecA for f f
  
  buildsRecA :: (Constraints t c, Applicative f) 
             => For c 
             -> (forall s. c s => FieldInfo (t -> s) -> f s) 
             -> (FieldInfo (t -> t) -> f t)
             -> [(CtorInfo, f t)]
  buildsRecA for sub _ = buildsA for sub


builds :: (ADT t, Constraints t c) 
       => For c -> (forall s. c s => FieldInfo (t -> s) -> s) -> [(CtorInfo, t)]
builds for f = fmap runIdentity <$> buildsA for (Identity . f)  

mbuilds :: forall t c m. (ADT t, Constraints t c, Monoid m) 
        => For c -> (forall s. c s => FieldInfo (t -> s) -> m) -> [(CtorInfo, m)]
mbuilds for f = fmap getConstant <$> ms
  where
    ms :: [(CtorInfo, Constant m t)]
    ms = buildsA for (Constant . f)


(!) :: t -> FieldInfo (t -> s) -> s
t ! info = project info t

at :: ADT t => [(a, b)] -> t -> b
at ab t = snd (ab !! ctorIndex t)


class Empty a where {}
instance Empty a

ctorInfo :: (ADT t, Constraints t Empty) => t -> CtorInfo
ctorInfo t = fst (builds (For :: For Empty) (t !) !! ctorIndex t)


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
  