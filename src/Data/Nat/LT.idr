module Data.Nat.LT

import public Control.Order.Strict
import public Control.Relation.Asymmetric
import public Control.Relation.Irreflexive
import public Data.Nat

%default total

export
Irreflexive Nat LT where
  irreflexive = succNotLTEpred

export
Transitive Nat LT where
  transitive {x = Z} {y = S y} _ (LTESucc _) = LTESucc LTEZero
  transitive {x = S x} {y = S y} {z = S z} (LTESucc xy) (LTESucc yz) =
    LTESucc $ transitive {rel = LT} xy yz

export
Asymmetric Nat LT where
  asymmetric LTEZero _ impossible
  asymmetric (LTESucc _) LTEZero impossible
  asymmetric {x = S x} {y = S y} (LTESucc xy) (LTESucc yx) =
    succNotLTEpred $ transitive {rel = LT} xy yx

export
Connex Nat LT where
  connex {x = Z} {y = Z} notEq = void $ notEq Refl
  connex {x = Z} {y = S y} _ = Left $ LTESucc LTEZero
  connex {x = S x} {y = Z} notEq = Right $ LTESucc LTEZero
  connex {x = S x} {y = S y} notEq =
    case connex {rel = LT} $ \xy => notEq $ cong S xy of
      Left lt => Left $ LTESucc lt
      Right gt => Right $ LTESucc gt

export
StrictLinearOrder Nat LT where
