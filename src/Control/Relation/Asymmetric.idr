module Control.Relation.Asymmetric

public export
interface Asymmetric ty rel where
  asymmetric : {x : ty} -> {y : ty} -> rel x y -> Not (rel y x)
