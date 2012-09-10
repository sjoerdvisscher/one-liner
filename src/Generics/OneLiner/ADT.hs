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
  , ScopedTypeVariables
  #-}
module Generics.OneLiner.ADT where
  
import Generics.OneLiner.Info

import GHC.Prim (Constraint)
import Control.Applicative
import Data.Functor.Identity
import Data.Functor.Constant
import Data.Monoid


data FieldInfo t s = FieldInfo
  { fieldName :: String
  , project   :: t -> s
  }

data For (c :: * -> Constraint) = For

class ADT t where

  ctorInfo :: t -> CtorInfo

  type Constraints t c :: Constraint
  buildsA :: (Constraints t c, Applicative f) 
          => For c -> (forall s. c s => FieldInfo t s -> f s) -> [f t]


builds :: (ADT t, Constraints t c) 
       => For c -> (forall s. c s => FieldInfo t s -> s) -> [t]
builds for f = fmap runIdentity $ buildsA for (Identity . f)  

mbuilds :: forall t c m. (ADT t, Constraints t c, Monoid m) 
        => For c -> (forall s. c s => FieldInfo t s -> m) -> [m]
mbuilds for f = fmap getConstant ms
  where
    ms :: [Constant m t]
    ms = buildsA for (Constant . f)


(!) :: t -> FieldInfo t s -> s
t ! FieldInfo _ proj = proj t

at :: ADT t => [a] -> t -> a
at as t = as !! ctorIndex (ctorInfo t)