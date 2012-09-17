{-# LANGUAGE TypeFamilies, DefaultSignatures, ConstraintKinds, OverlappingInstances #-}

import Generics.OneLiner.ADT

import Control.Applicative

data Company  = C [Dept]               deriving (Eq, Read, Show)               
data Dept     = D Name Manager [Unit]  deriving (Eq, Read, Show)
data Unit     = PU Employee | DU Dept  deriving (Eq, Read, Show)
data Employee = E Person Salary        deriving (Eq, Read, Show)
data Person   = P Name Address         deriving (Eq, Read, Show)
data Salary   = S Float                deriving (Eq, Read, Show)                  
type Manager  = Employee 
type Name     = String
type Address  = String

-- An illustrative company
genCom :: Company
genCom = C [D "Research" laemmel [PU joost, PU marlow],
            D "Strategy" blair   []]

-- A typo for the sake of testing equality;
-- (cf. lammel vs. laemmel)
genCom' :: Company
genCom' = C [D "Research" lammel [PU joost, PU marlow],
             D "Strategy" blair   []]

lammel, laemmel, joost, marlow, blair :: Employee
lammel  = E (P "Lammel" "Amsterdam") (S 8000)
laemmel = E (P "Laemmel" "Amsterdam") (S 8000)
joost   = E (P "Joost"   "Amsterdam") (S 1000)
marlow  = E (P "Marlow"  "Cambridge") (S 2000)
blair   = E (P "Blair"   "London")    (S 100000)


instance ADT Company where
  type Constraints Company c = c [Dept]
  buildsA For f = [(ctor "C", C <$> f (FieldInfo $ \(C l) -> l))]

instance ADT Dept where
  type Constraints Dept c = (c Name, c Manager, c [Unit])
  buildsA For f = [(ctor "D", D 
    <$> f (FieldInfo $ \(D n _ _) -> n) 
    <*> f (FieldInfo $ \(D _ m _) -> m) 
    <*> f (FieldInfo $ \(D _ _ u) -> u))]

instance ADT Unit where
  ctorIndex PU{} = 0
  ctorIndex DU{} = 1
  type Constraints Unit c = (c Employee, c Dept)
  buildsA For f = 
    [ (ctor "PU", PU <$> f (FieldInfo $ \(PU e) -> e))
    , (ctor "DU", DU <$> f (FieldInfo $ \(DU d) -> d))
    ]

instance ADT Employee where
  type Constraints Employee c = (c Person, c Salary)
  buildsA For f = [(ctor "E", E <$> f (FieldInfo $ \(E p _) -> p) <*> f (FieldInfo $ \(E _ s) -> s))]

instance ADT Person where
  type Constraints Person c = (c Name, c Address)
  buildsA For f = [(ctor "P", P <$> f (FieldInfo $ \(P n _) -> n) <*> f (FieldInfo $ \(P _ a) -> a))]

instance ADT Salary where
  type Constraints Salary c = (c Float)
  buildsA For f = [(ctor "S", S <$> f (FieldInfo $ \(S s) -> s))]
  
class IncreaseSalary t where
  increaseSalary :: Float -> t -> t
  default increaseSalary :: (ADT t, Constraints t IncreaseSalary) => Float -> t -> t
  increaseSalary k t = builds (For :: For IncreaseSalary) (\info -> increaseSalary k (t ! info)) `at` t

instance IncreaseSalary Company
instance IncreaseSalary Dept
instance IncreaseSalary Unit
instance IncreaseSalary Employee
instance IncreaseSalary Person where
  increaseSalary _ = id
instance IncreaseSalary Salary where
  increaseSalary k (S s) = S (s * (1+k))
instance IncreaseSalary a => IncreaseSalary [a]
instance IncreaseSalary String where
  increaseSalary _ = id
  
main :: IO ()
main = print $ increaseSalary 0.1 genCom
