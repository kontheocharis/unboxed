module Core where

import Context (Idx (..), Lvl, Name, Names (..))
import Data.Kind (Type)
import Data.Singletons (Sing)

data Nat = Z | S Nat

newtype MetaVar = MetaVar Name

data Spine :: Nat -> Type -> Type where
  Lin :: Spine Z t
  Snoc :: Spine n t -> Tm ns -> Spine (S n) t

data Stage = Obj | Mta

data Binder :: Stage -> Name -> Names -> Type where
  Lam :: Binder s n ns
  -- rhs
  Let :: Tm ns -> Binder s n ns
  -- rhs
  LetIrr :: Tm ns -> Binder Obj n ns
  -- a, b, A
  PiObj :: Tm ns -> Tm ns -> Tm ns -> Binder Obj n ns
  -- A
  PiMeta :: Tm ns -> Binder Mta n ns

data Tm :: Names -> Type where
  Var :: Idx ns -> Tm ns
  Meta :: MetaVar -> Tm ns
  App :: Tm ns -> Spine k t -> Tm ns
  Bind :: Sing s -> Sing n -> Binder s n ns -> Tm (ns :< n) -> Tm ns
  Prim :: Prim k ns -> Spine k (Tm ns) -> Tm ns

data Env :: Names -> Names -> Type where
  ELin :: Env ns Empty
  ESnoc :: Env ns ms -> Val ns -> Env ns (ms :< m)

data Closure :: Name -> Names -> Type where
  Cl :: Env ns ms -> Tm (ms :< n) -> Closure n ns

data Val :: Names -> Type where
  VRigid :: Lvl ns -> Spine k t -> Val ns
  VFlex :: MetaVar -> Spine k t -> Val ns
  VBind :: Sing s -> Sing n -> Binder s n ns -> Closure n ns -> Val ns
  VPrim :: Prim k ns -> Spine k (Val ns) -> Val ns

data Prim :: Nat -> Names -> Type where
  Typ :: Prim Z ns
  TYP :: Prim (S Z) ns
  Unsized :: Prim (S Z) ns
  IrrT :: Prim (S Z) ns
  Irr :: Prim (S Z) ns
  Code :: Prim (S Z) ns
  Quote :: Prim (S Z) ns
  Splice :: Prim (S Z) ns
  Bytes :: Prim Z ns
  BYTES :: Prim Z ns
  EmbBYTES :: Prim (S Z) ns
  Ptr :: Prim Z ns
  Size :: Prim Z ns
  Zero :: Prim Z ns
  PlusBYTES :: Prim (S (S Z)) ns
  PlusBytes :: Prim (S (S Z)) ns -- could probably merge
  PadT :: Prim (S Z) ns
  Pad :: Prim Z ns
  Make :: Prim (S Z) ns
  Box :: Prim (S Z) ns
  Give :: Prim (S Z) ns
  Bool :: Prim Z ns
  BOOL :: Prim Z ns
  True :: Prim Z ns
  False :: Prim Z ns
  TRUE :: Prim Z ns
  FALSE :: Prim Z ns
  Nat :: Prim Z ns
  NAT :: Prim Z ns
  Ze :: Prim Z ns
  Su :: Prim (S Z) ns
  ZE :: Prim Z ns
  SU :: Prim (S Z) ns

typeof :: Prim k ns -> (Spine k (Tm ns), Tm ns)
typeof = _
