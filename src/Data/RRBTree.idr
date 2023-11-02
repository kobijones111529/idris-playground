module Data.RRBTree

import Data.Fin
import Data.Vect

%default total

-- data Minus : (minuend : Nat) -> (subtrahend : Nat) -> Type where
--   MkMinus : {difference : Nat} -> {subtrahend : Nat} -> Minus (difference + subtrahend) subtrahend

-- Uninhabited (Minus Z (S n)) where
--   uninhabited (MkMinus {difference = Z} {subtrahend = S _}) impossible

-- Uninhabited (Minus n m) => Uninhabited (Minus (S n) (S m)) where
--   uninhabited (MkMinus {difference = Z} {subtrahend = S n}) @{ab} = ?h2
--   uninhabited (MkMinus {difference = S d} {subtrahend = S n}) @{ab} = ?h3

-- minus'' : (a : Nat) -> (b : Nat) -> Dec (Minus a b)
-- minus'' a Z = rewrite sym $ plusZeroRightNeutral a in Yes MkMinus
-- minus'' Z (S b) = No absurd
-- minus'' (S a) (S b) with (minus'' a b)
--   minus'' (S (a + b)) (S b) | Yes MkMinus = ?h
--   _ | No r = ?minus''_1

minus' : (left : Nat) -> (right : Nat) -> {auto 0 lte : LTE right left} -> Nat
minus' left Z = left
minus' (S left) (S right) {lte = LTESucc _} = minus' left right

a : Nat
a = 2

minus'Plus : (m : Nat) -> minus' (plus m n) m {lte = lteAddRight {m = n} m} = n
minus'Plus Z = Refl
minus'Plus (S k) = minus'Plus k

minus'SuccSucc : (m : Nat) -> (n : Nat) -> {auto 0 lte : LTE n m} -> minus' (S m) (S n) = minus' m n
minus'SuccSucc _ _ = Refl

minus'ZeroRight : (left : Nat) -> minus' left 0 = left
minus'ZeroRight left = Refl

lteReflects : (n : Nat) -> lte n n = True
lteReflects Z     = Refl
lteReflects (S n) = rewrite lteReflects n in Refl

minus'OneSuccN : (n : Nat) -> S Z = minus' (S n) n {lte = lteSuccRight $ lteReflectsLTE n n (lteReflects n)}
-- minus'OneSuccN Z = Refl
-- minus'OneSuccN (S n) = rewrite minus'SuccSucc (S n) n in minus'OneSuccN n

plusMinus' : (m : Nat) -> {n : Nat} -> {auto 0 lte : LTE n m} -> plus n (minus' m n) = m
plusMinus' Z {n = Z} = Refl
plusMinus' (S m) {n = Z} = Refl
plusMinus' (S m) {n = (S n)} {lte = LTESucc lte} =
    rewrite plusMinus' m {n}
    in Refl

minus'Succ : (m : Nat) -> (n : Nat) -> {auto 0 lte : LTE n m} -> S (minus' m n) = minus' (S m) n {lte = lteSuccRight lte}
-- minus'Succ _ Z = Refl
-- minus'Succ (S m) (S n) {lte = LTESucc lte} = ?h

minusSucc : (m : Nat) -> (n : Nat) -> {auto 0 lte : LTE n m} -> minus (S m) n = S (minus m n)
minusSucc m Z = rewrite minusZeroRight m in Refl
minusSucc (S m) (S n) {lte = LTESucc lte} = rewrite minusSucc m n in Refl

plusSum : Foldable t => (xs : t Nat) -> (n : Nat) -> n + foldl (\acc, elem => acc + elem) 0 xs = foldl (\acc, elem => acc + elem) n xs

-- minus'Strengthens :
--   (a : Nat) ->
--   (b : Nat) ->
--   (upper : Nat) ->
--   (lte : LTE b a) ->
--   (lteUpper : LTE a upper) ->
--   LTE (minus' a b) (minus' upper b {lte = transitive lte lteUpper})
-- minus'Strengthens _ Z _ _ lteUpper = lteUpper
-- minus'Strengthens (S a) (S b) (S upper) (LTESucc lte) (LTESucc lteUpper) = minus'Strengthens a b upper ?l ?l'

-- test : Nat
-- test =
--   let
--     a = 3
--     b = 2

fn : Bool -> Nat
fn False = 4
fn True = 3

getSize : Vect _ (DPair Nat _) -> Nat -> Nat
getSize xs offset = foldl (\acc, elem => plus acc elem) offset (map fst xs)

data RRBTreeNode : (depth : Nat) -> (size : Nat) -> ty -> Type where
  Leaf : {relaxed : Bool} -> Vect (fn relaxed) ty -> RRBTreeNode 0 (fn relaxed) ty
  Internal :
    {relaxed : Bool} ->
    (nodes : Vect (fn relaxed) (size ** RRBTreeNode lvl size ty)) ->
    RRBTreeNode (S lvl) (getSize nodes 0) ty

mutual
  data RRBTreeNodeLeft : (depth : Nat) -> (size : Nat) -> ty -> Type where
    LeftLeaf :
      {len : Nat} ->
      {auto 0 low : LTE 1 len} ->
      {auto 0 high : LTE len 4} ->
      Vect len ty ->
      RRBTreeNodeLeft 0 len ty
    LeftInternal :
      {len : Nat} ->
      {auto 0 high : LTE len 3} ->
      (nodes : Vect len (size ** RRBTreeNode lvl size ty)) ->
      {size : Nat} ->
      RRBTreeNodeLeft lvl size ty ->
      RRBTreeNodeLeft (S lvl) (getSize nodes 0 + size) ty

data RRBTree : ty -> (size : Nat) -> Type where
  Root : RRBTreeNodeLeft lvl size ty -> RRBTree ty size

plusLteMonotoneLeftLeft : (p : Nat) -> (q : Nat) -> (r : Nat) -> LTE (p + q) (p + r) -> LTE q r

f :
  (rem : Nat) ->
  (xs : Vect n (size ** RRBTreeNode depth size ty)) ->
  {lsize : Nat} ->
  (x : RRBTreeNodeLeft depth lsize ty) ->
  {auto prf : rem `LT` (getSize xs 0 + lsize)} ->
  Either (Fin lsize, RRBTreeNodeLeft depth lsize ty) (size ** (Fin size, RRBTreeNode depth size ty))
f rem [] x = Left (natToFinLT rem, x)
f rem ((size ** x) :: xs) left {prf} = case rem `isLT` size of
  Yes _ => Right (size ** (natToFinLT rem, x))
  No notLT =>
    let
      -- hlp : (r : Nat) -> {auto 0 lte : LTE size r} -> r = plus size (minus' r size)

      lte = fromLteSucc . notLTEImpliesGT $ notLT
      lteSucc = lteSuccRight lte
      ac = plusLteMonotoneLeftLeft size (minus' (S rem) size {lte = lteSucc}) (getSize xs 0 + lsize) (rewrite plusMinus' (S rem) {n = size} in ?he)
      -- ab = plusLteMonotoneLeftLeft size (minus' (S rem) size {lte = lteSucc}) (getSize xs 0 + lsize) (rewrite plusMinus' (S rem) {n = size} in rewrite plusSum (map fst xs) size in ?h1)
      ad = plusLteMonotoneLeftLeft size (minus' (S rem) size {lte = lteSucc}) (getSize xs 0 + lsize) (rewrite plusMinus' (S rem) {n = size} in rewrite plusAssociative size (getSize xs 0) lsize in ?h1)
      -- ab = plusLteMonotoneLeftLeft size (minus' (S rem) size {lte = lteSucc}) (getSize xs 0 + lsize) (rewrite plusMinus' (S rem) {n = size} in rewrite plusAssociative size (getSize xs 0) lsize in rewrite plusSum (map fst xs) size in ?h1)
    in f (minus' rem size {lte = lte}) xs left {prf = ?hel}

index : (i : Nat) -> {size : Nat} -> {auto _ : i `LT` size} -> RRBTree ty size -> ty
index i (Root (LeftLeaf xs)) = index (natToFinLT i) xs
index i (Root (LeftInternal xs x)) =
  let a = f i xs x
  in case a of
    Left rem => indexLeft ?s x
    Right (size ** (rem, node)) => ?b--index rem node
  where


    prf : (a : Nat) -> (b : Nat) -> {auto 0 _ : a `LT` c} -> (a `minus` b) `LT` (c `minus` b)

    index : {size : Nat} -> (i : Nat) -> {auto 0 _ : i `LT` size} -> RRBTreeNode lvl size ty -> ty

    indexLeft : {size : Nat} -> Fin size -> RRBTreeNodeLeft lvl size ty -> ty

