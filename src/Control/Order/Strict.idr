module Control.Order.Strict

import public Control.Order
import public Control.Relation
import public Control.Relation.Asymmetric
import public Control.Relation.Irreflexive

public export
interface (Irreflexive ty rel, Asymmetric ty rel, Transitive ty rel, Connex ty rel) => StrictLinearOrder ty rel where
