module Data.Nat.FastLTE

import Control.Relation
import Data.Nat

%default total

public export
data FastLTE : Nat -> Nat -> Type where
  MkFastLTE : (n : Nat) -> (diff : Nat) -> FastLTE n (n + diff)

export
Uninhabited (FastLTE (S n) Z) where
  uninhabited (MkFastLTE _ _) impossible

public export
fastLTESucc : FastLTE m n -> FastLTE (S m) (S n)
fastLTESucc (MkFastLTE m diff) = MkFastLTE (S m) diff

namespace LTE
  public export
  data View : FastLTE m n -> Type where
    LTEZero : View (MkFastLTE Z n)
    LTESucc : (lte : FastLTE m n) -> View (fastLTESucc lte)

  export
  view : (lte : FastLTE m n) -> View lte
  view (MkFastLTE Z _) = LTEZero
  view (MkFastLTE (S m) diff) = LTESucc (MkFastLTE m diff)

public export
FastLT : Nat -> Nat -> Type
FastLT m n = FastLTE (S m) n

namespace LT
  public export
  data View : FastLT m n -> Type where
    LTZero : View (MkFastLTE (S Z) n)
    LTSucc : (lt : FastLT m n) -> View (fastLTESucc lt)

  export
  view : (lt : FastLT m n) -> LT.View lt
  view (MkFastLTE (S Z) n) = LTZero
  view (MkFastLTE (S (S m)) n) = LTSucc (MkFastLTE (S m) n)

export
Uninhabited (FastLTE m n) => Uninhabited (FastLTE (S m) (S n)) where
  uninhabited lte with (LTE.view lte)
    uninhabited (MkFastLTE Z _) | LTEZero impossible
    uninhabited _ | LTESucc lte = absurd lte

public export
Reflexive Nat FastLTE where
  reflexive = replace {p = FastLTE _} (plusZeroRightNeutral _) (MkFastLTE _ Z)

public export
Antisymmetric Nat FastLTE where
  antisymmetric xy yx with (LTE.view xy)
    antisymmetric (MkFastLTE Z Z) (MkFastLTE Z Z) | LTEZero = Refl
    antisymmetric (MkFastLTE Z (S _)) (MkFastLTE (S _) Z) | LTEZero impossible
    antisymmetric _ yx | (LTESucc xy) with (LTE.view yx)
      antisymmetric _ _ | LTESucc xy | (LTESucc yx) =
        cong S $ antisymmetric xy yx
