module Control.Relation.Erased

import public Control.Relation

export
0 reflexive : Reflexive ty rel => rel x x
reflexive = Control.Relation.reflexive

export
0 transitive : Transitive ty rel => (0 xy : rel x y) -> (0 yz : rel y z) -> rel x z
transitive xy yz = Control.Relation.transitive xy yz

export
0 symmetric : Symmetric ty rel => (0 xy : rel x y) -> rel y x
symmetric xy = Control.Relation.symmetric xy

export
0 antisymmetric : Antisymmetric ty rel => (0 xy : rel x y) -> (0 yx : rel y x) -> x = y
antisymmetric xy yx = Control.Relation.antisymmetric xy yx
