{-# LANGUAGE TypeFamilies, DefaultSignatures, ConstraintKinds #-}

import Generics.OneLiner.ADT
import Data.Monoid

class Size t where
  
  size :: t -> Int
  
  default size :: (ADT t, Constraints t Size) => t -> Int
  size t = getSum $ mbuilds (For :: For Size) (\fld -> Sum $ size (t ! fld)) `at` t