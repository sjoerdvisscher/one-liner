{-# LANGUAGE TypeFamilies, DefaultSignatures, ConstraintKinds, TypeOperators #-}

import Generics.OneLiner.ADT
import Generics.OneLiner.Functions

import Data.Monoid
import Control.Applicative

import Text.Read (readPrec)


class Size t where
  
  size :: t -> Int
  
  default size :: (ADT t, Constraints t Size) => t -> Int
  size = succ . getSum . gfoldMap (For :: For Size) (Sum . size)
  
instance Size Bool
instance Size a => Size (Maybe a)


class EnumAll t where
  
  enumAll :: [t]
  
  default enumAll :: (ADT t, Constraints t EnumAll) => [t]
  enumAll = concat $ buildsA (For :: For EnumAll) (const enumAll)

instance EnumAll Bool
instance EnumAll a => EnumAll (Maybe a)


infixr 5 :^:
data Tree a = Leaf { value :: a } | Tree a :^: Tree a

instance ADT (Tree a) where
  
  ctorIndex Leaf{}  = 0
  ctorIndex (_:^:_) = 1
  ctorInfo _ 0 = CtorInfo "Leaf" True Prefix
  ctorInfo _ 1 = CtorInfo ":^:"  False (Infix RightAssociative 5)
  
  type Constraints (Tree a) c = (c a, c (Tree a))
  buildsRecA For sub rec = 
    [ Leaf <$> sub (SelectorInfo "value" value)
    , (:^:) <$> rec (FieldInfo (\(l :^: _) -> l)) <*> rec (FieldInfo (\(_ :^: r) -> r))
    ]

instance Show a => Show (Tree a) where showsPrec = showsPrecADT
instance Read a => Read (Tree a) where readPrec = readPrecADT
instance Size a => Size (Tree a)
instance EnumAll a => EnumAll (Tree a)

trees :: [Tree (Maybe Bool)]
trees = enumAll

sizes :: [Int]
sizes = map size trees
