module Decidable.Ordering

import public Control.Order
import public Decidable.Equality

public export
data DecOrd : Connex ty rel => (x, y : ty) -> Type where
  LT : Connex ty rel => rel x y -> DecOrd {rel} x y
  EQ : Connex ty rel => x = y -> DecOrd {rel} x y
  GT : Connex ty rel => rel y x -> DecOrd {rel} x y

public export
decOrd : (Connex ty rel, DecEq ty) => (x, y : ty) -> DecOrd {rel} x y
decOrd x y =
  case x `decEq` y of
    Yes prf => EQ prf
    No contra =>
      case connex {rel} contra of
        Left prf => LT prf
        Right prf => GT prf
