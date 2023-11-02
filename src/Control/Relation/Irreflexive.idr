module Control.Relation.Irreflexive

public export
interface Irreflexive ty rel where
  irreflexive : {x : ty} -> Not (rel x x)
