{-# LANGUAGE
    TypeFamilies
  , DeriveGeneric
  , ConstraintKinds
  , FlexibleContexts
  , FlexibleInstances
  , DefaultSignatures
  , OverlappingInstances
  #-}

import GHC.Generics
import Generics.OneLiner


data Company  = C [Dept]               deriving (Eq, Read, Show, Generic)
data Dept     = D Name Manager [Unit]  deriving (Eq, Read, Show, Generic)
data Unit     = PU Employee | DU Dept  deriving (Eq, Read, Show, Generic)
data Employee = E Person Salary        deriving (Eq, Read, Show, Generic)
data Person   = P Name Address         deriving (Eq, Read, Show, Generic)
data Salary   = S Float                deriving (Eq, Read, Show, Generic)
type Manager  = Employee
type Name     = String
type Address  = String

-- An illustrative company
genCom :: Company
genCom = C [D "Research" laemmel [PU joost, PU marlow],
            D "Strategy" blair   []]

laemmel, joost, marlow, blair :: Employee
laemmel = E (P "Laemmel" "Amsterdam") (S 8000)
joost   = E (P "Joost"   "Amsterdam") (S 1000)
marlow  = E (P "Marlow"  "Cambridge") (S 2000)
blair   = E (P "Blair"   "London")    (S 100000)


class IncreaseSalary t where
  increaseSalary :: Float -> t -> t
  default increaseSalary :: (ADT t, Constraints t IncreaseSalary) => Float -> t -> t
  increaseSalary k = gmap (For :: For IncreaseSalary) (increaseSalary k)

instance IncreaseSalary Company
instance IncreaseSalary Dept
instance IncreaseSalary Unit
instance IncreaseSalary Employee
instance IncreaseSalary Person
instance IncreaseSalary Salary where
  increaseSalary k (S s) = S (s * (1+k))
instance IncreaseSalary a => IncreaseSalary [a]
instance IncreaseSalary String where
  increaseSalary _ = id

main :: IO ()
main = print $ increaseSalary 0.1 genCom
