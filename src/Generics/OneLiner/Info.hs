-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner.Info
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Generics.OneLiner.Info where

data CtorInfo = CtorInfo
  { ctorName  :: String
  , isRecord  :: Bool
  , fixity    :: Fixity
  }
  deriving (Eq, Show, Ord, Read)

ctor :: String -> CtorInfo
ctor name = CtorInfo name False Prefix

data Fixity = Prefix | Infix Associativity Int
  deriving (Eq, Show, Ord, Read)

data Associativity = LeftAssociative | RightAssociative | NotAssociative
  deriving (Eq, Show, Ord, Read)

data FieldInfo p
  = SelectorInfo
    { selectorName :: String
    , project      :: p
    }
  | FieldInfo
    { project      :: p
    }

instance Functor FieldInfo where
  fmap f (SelectorInfo s p) = SelectorInfo s (f p)
  fmap f (FieldInfo p) = FieldInfo (f p)
