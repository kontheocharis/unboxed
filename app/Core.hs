{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Core where

import Context (Idx (..), Lvl, Name, Names (..), PiMode (..), type (+++))
import Data.Data (Proxy (..), type (:~:) (Refl))
import Data.Kind (Type)
import Data.Singletons (Sing)
import Data.Type.Equality ((:~:))

data Nat = Z | S Nat

newtype MetaVar = MetaVar Name

type Arity = Names

data Spine :: Type -> Arity -> Type where
  Nil :: Spine t Empty
  Cons :: t -> Spine t as -> Spine t (as :< a)

data Tel :: (Names -> Type) -> Arity -> Names -> Type where
  TNil :: Tel f Empty ms
  TCons :: forall {ms} m {f} {as}. f ms -> Tel f as (ms :< m) -> Tel f ((Empty :< m) +++ as) ms

data Stage = Obj | Mta

data Binder :: Stage -> (PiMode, Name) -> Names -> Type where
  Lam :: Binder s n ns
  -- rhs
  Let :: Tm ns -> Binder s n ns
  -- rhs
  LetIrr :: Tm ns -> Binder Obj n ns
  -- a, b, A
  PiObj :: Tm ns -> Tm ns -> Tm ns -> Binder Obj n ns
  -- A
  PiMta :: Tm ns -> Binder Mta n ns

data Tm :: Names -> Type where
  Var :: Idx ns -> Tm ns
  Meta :: MetaVar -> Tm ns
  App :: Tm ns -> Spine k t -> Tm ns
  Bind :: Sing s -> Sing n -> Binder s n ns -> Tm (ns :< n) -> Tm ns
  Prim :: Prim ks ns -> Spine (Tm ns) ks -> Tm ns

type Env ms ns = Tel Val ns ms

data Closure :: (PiMode, Name) -> Names -> Type where
  Cl :: Env ns ms -> Tm (ms :< n) -> Closure n ns

data Val :: Names -> Type where
  VRigid :: Lvl ns -> Spine k t -> Val ns
  VFlex :: MetaVar -> Spine k t -> Val ns
  VBind :: Sing s -> Sing n -> Binder s n ns -> Closure n ns -> Val ns
  VPrim :: Prim ks ns -> Spine (Val ns) ks -> Val ns

-- No need to deal with deBrujin
class In (n :: Name) (ns :: Names) where
  find :: Proxy n -> Idx ns

  var :: Proxy n -> Tm ns
  var x = Var (find x)

instance In n (ns :< '(m, n)) where
  find _ = IZ

instance {-# OVERLAPS #-} (In n ns) => In n (ns :< n') where
  find x = IS (find x)

data Prim :: Arity -> Names -> Type where
  PrimTYP :: Prim Empty ns
  PrimTyp :: Prim (Empty :< '(Explicit, "bytes")) ns -- this is unsized
  PrimIrrT :: Prim (Empty :< '(Implicit, "bytes") :< '(Explicit, "ty")) ns
  PrimIrr :: Prim (Empty :< '(Implicit, "bytes") :< '(Implicit, "ty") :< '(Explicit, "val")) ns
  PrimCode :: Prim (Empty :< '(Implicit, "bytes") :< '(Explicit, "ty")) ns
  PrimQuote :: Prim (Empty :< '(Implicit, "bytes") :< '(Implicit, "ty") :< '(Explicit, "val")) ns
  PrimSplice :: Prim (Empty :< '(Implicit, "bytes") :< '(Implicit, "ty") :< '(Explicit, "val")) ns
  PrimBytes :: Prim Empty ns
  PrimBYTES :: Prim Empty ns
  PrimEmbBYTES :: Prim (Empty :< '(Explicit, "bytes")) ns
  PrimPtr :: Prim Empty ns
  PrimSize :: Prim Empty ns
  PrimZero :: Prim Empty ns
  PrimPlusBYTES :: Prim (Empty :< '(Explicit, "a") :< '(Explicit, "b")) ns
  PrimPlusBytes :: Prim (Empty :< '(Explicit, "a") :< '(Explicit, "b")) ns -- could probably merge
  PrimPadT :: Prim (Empty :< '(Explicit, "bytes")) ns
  PrimPad :: Prim (Empty :< '(Implicit, "bytes")) ns
  PrimMake :: Prim (Empty :< '(Implicit, "bytes") :< '(Explicit, "ty")) ns
  PrimBox :: Prim (Empty :< '(Explicit, "x")) ns
  PrimGive :: Prim (Empty :< '(Explicit, "x")) ns
  PrimBool :: Prim Empty ns
  PrimBOOL :: Prim Empty ns
  PrimTrue :: Prim Empty ns
  PrimFalse :: Prim Empty ns
  PrimTRUE :: Prim Empty ns
  PrimFALSE :: Prim Empty ns
  PrimNat :: Prim Empty ns
  PrimNAT :: Prim Empty ns
  PrimZe :: Prim Empty ns
  PrimSu :: Prim (Empty :< '(Explicit, "n")) ns
  PrimZE :: Prim Empty ns
  PrimSU :: Prim (Empty :< '(Explicit, "n")) ns

pattern Bytes :: Tm ns
pattern Bytes = Prim PrimBytes Nil

pattern BYTES :: Tm ns
pattern BYTES = Prim PrimBYTES Nil

pattern TYP :: Tm ns
pattern TYP = Prim PrimTYP Nil

pattern UnsizedTyp :: Tm ns -> Tm ns
pattern UnsizedTyp b = Prim PrimTyp (Cons b Nil)

pattern SizedTyp :: Tm ns -> Tm ns
pattern SizedTyp b = Prim PrimTyp (Cons (Prim PrimEmbBYTES (Cons b Nil)) Nil)

pattern IrrTyp :: Tm ns
pattern IrrTyp = SizedTyp (Prim PrimZero Nil)

pattern IrrT :: Tm ns -> Tm ns -> Tm ns
pattern IrrT b c = Prim PrimIrrT (Cons b (Cons c Nil))

pattern Code :: Tm ns -> Tm ns -> Tm ns
pattern Code b c = Prim PrimCode (Cons b (Cons c Nil))

pattern Size :: Tm ns
pattern Size = Prim PrimSize Nil

primType :: Prim ks ns -> (Tel Tm ks ns, Tm (ns +++ ks))
primType PrimTYP = (TNil, TYP)
primType PrimTyp = (TCons Bytes TNil, IrrTyp)
primType PrimIrrT =
  ( TCons @"bytes" Bytes (TCons (UnsizedTyp (var @"bytes" Proxy)) TNil),
    IrrTyp
  )
primType PrimIrr =
  ( TCons @"bytes"
      BYTES
      ( TCons @"ty"
          (SizedTyp (var @"bytes" Proxy))
          (TCons (var @"ty" Proxy) TNil)
      ),
    IrrT (var @"bytes" Proxy) (var @"ty" Proxy)
  )
primType PrimCode =
  ( TCons @"bytes"
      Bytes
      (TCons (UnsizedTyp (var @"bytes" Proxy)) TNil),
    TYP
  )
primType PrimQuote =
  ( TCons @"bytes"
      BYTES
      ( TCons @"ty"
          (SizedTyp (var @"bytes" Proxy))
          (TCons (var @"ty" Proxy) TNil)
      ),
    Code (var @"bytes" Proxy) (var @"ty" Proxy)
  )
primType PrimSplice =
  ( TCons @"bytes"
      BYTES
      ( TCons @"ty"
          (SizedTyp (var @"bytes" Proxy))
          (TCons (Code (var @"bytes" Proxy) (var @"ty" Proxy)) TNil)
      ),
    var @"ty" Proxy
  )
primType PrimBytes = (TNil, SizedTyp Size)
primType PrimBYTES = (TNil, TYP)
primType PrimEmbBYTES = (TCons BYTES TNil, Bytes)
primType PrimPtr = (TNil, BYTES)
primType PrimSize = (TNil, BYTES)
primType PrimZero = (TNil, BYTES)
primType PrimPlusBYTES = (TCons BYTES (TCons BYTES TNil), BYTES)
primType PrimPlusBytes = (TCons Bytes (TCons Bytes TNil), Bytes)

-- primType PrimPadT = (
