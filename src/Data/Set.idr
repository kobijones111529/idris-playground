module Data.Set

import Data.DPair
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

public export
data Unique : List a -> Type where
  Empty : Unique []
  IsUnique : (0 headUnique : Not (Elem x xs)) -> (0 tailUnique : Unique xs) -> Unique (x :: xs)

export
Nil : Unique []
Nil = Empty

export
(::) : {0 tail : List a} -> (x : Subset a (Not . flip Elem tail)) -> (xs : Unique tail) -> Unique (x.fst :: tail)
(::) (Element x el) unique = IsUnique el unique

namespace View
  public export
  data View : Unique xs -> Type where
    Nil : View Empty
    (::) :
      {0 tail : List a} ->
      (x : Subset a (\x => Not $ Elem x tail)) ->
      (xs : Unique tail) ->
      View (x :: xs)

export
toUnique : DecEq a => List a -> Subset (List a) Unique
toUnique [] = (Element [] Empty)
toUnique (x :: xs) with (toUnique xs)
  _ | (Element xs' unique) = case isElem x xs' of
    Yes elem => Element xs' unique
    No notElem => Element (x :: xs') (IsUnique notElem unique)

export
toUniqueTailRec : DecEq a => List a -> Subset (List a) Unique
toUniqueTailRec xs = go xs $ Element [] Empty
  where
    go : List a -> Subset (List a) Unique -> Subset (List a) Unique
    go [] unique = unique
    go (x :: xs) (Element xs' unique) = case isElem x xs' of
      Yes elem => go xs $ Element xs' unique
      No notElem => go xs $ Element (x :: xs') (IsUnique notElem unique)
