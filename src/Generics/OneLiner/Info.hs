-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.OneLiner.Info
-- Copyright   :  (c) Sjoerd Visscher 2012
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  sjoerd@w3future.com
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------
module Generics.OneLiner.Info where

data CtorInfo = CtorInfo
  { ctorName  :: String
  , ctorIndex :: Int
  , fixity    :: Fixity
  }
  deriving (Eq, Show, Ord, Read)

data Fixity = Prefix | Infix Associativity Int
  deriving (Eq, Show, Ord, Read)

data Associativity = LeftAssociative | RightAssociative | NotAssociative
  deriving (Eq, Show, Ord, Read)
