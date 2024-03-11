module Data.FingerTree.Core

import Data.Nat
import Data.Vect

%default total

public export
record Node ty where
  constructor MkNode
  {n : Nat}
  {auto 0 lower : LTE 2 n}
  {auto 0 upper : LTE n 3}
  vect : Vect n ty

public export
record Affix ty where
  constructor MkAffix
  {n : Nat}
  {auto 0 lower : LTE 1 n}
  {auto 0 upper : LTE n 4}
  vect : Vect n ty

public export
data FingerTree : Type -> Type where
  Empty : FingerTree ty
  Single : ty -> FingerTree ty
  Deep :
    Affix ty ->
    FingerTree (Node ty) ->
    Affix ty ->
    FingerTree ty

public export
data NonEmpty : FingerTree ty -> Type where
  SingleIsNonEmpty : NonEmpty (Single x)
  DeepIsNonEmpty : NonEmpty (Deep left deep right)

Uninhabited (NonEmpty Empty) where
  uninhabited SingleIsNonEmpty impossible
  uninhabited DeepIsNonEmpty impossible

public export
isNonEmpty : (xs : FingerTree ty) -> Dec (NonEmpty xs)
isNonEmpty Empty = No uninhabited
isNonEmpty (Single x) = Yes SingleIsNonEmpty
isNonEmpty (Deep x y z) = Yes DeepIsNonEmpty

export
Show ty => Show (Node ty) where
  show (MkNode vect) = show vect

export
Show ty => Show (Affix ty) where
  show (MkAffix vect) = show vect

export
Show ty => Show (FingerTree ty) where
  show Empty = "[]"
  show (Single x) = "[\{show x}]"
  show (Deep left deep right) = "[\{show left} \{show deep} \{show right}]"
