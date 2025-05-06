module Context (Name, Names (..), Idx (..), Lvl (..)) where

import Data.Kind (Type)

type Name = String

data Names :: Type where
  Empty :: Names
  (:<) :: Names -> Name -> Names

infixr 5 :<

data Idx :: Names -> Type where
  IZ :: Idx Empty
  IS :: Idx ns -> Idx (ns :< n)

data Lvl :: Names -> Type where
  LZ :: Lvl Empty
  LS :: Lvl ns -> Lvl (ns :< n)
