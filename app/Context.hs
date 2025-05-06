module Context (Name, Names (..), Idx (..), Lvl (..), type (+++), PiMode (..)) where

import Data.Kind (Type)
import GHC.Base (Symbol)

type Name = Symbol

data PiMode = Explicit | Implicit

data Names :: Type where
  Empty :: Names
  (:<) :: Names -> (PiMode, Name) -> Names

type family (as :: Names) +++ (bs :: Names) :: Names where
  ys +++ (xs :< x) = (ys +++ xs) :< x
  ys +++ Empty = ys
  Empty +++ ys = ys

infixr 5 +++

infixl 5 :<

data Idx :: Names -> Type where
  IZ :: Idx (ns :< n)
  IS :: Idx ns -> Idx (ns :< n)

data Lvl :: Names -> Type where
  LZ :: Lvl (ns :< n)
  LS :: Lvl ns -> Lvl (ns :< n)
