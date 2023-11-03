module Data.RedBlackTree.Core

import public Control.Order.Strict
import public Decidable.Equality

%default total

public export
data Bound ty = Bottom | Middle ty | Top

public export
data BoundedRel : {0 rel : ty -> ty -> Type} -> Bound ty -> Bound ty -> Type where
  LTEBottomTop : BoundedRel Bottom Top
  LTEBottom : {x : ty} -> BoundedRel Bottom (Middle x)
  LTETop : {x : ty} -> BoundedRel (Middle x) Top
  LTEMiddle : {0 rel : ty -> ty -> Type} -> {x, y : ty} -> rel x y -> BoundedRel {rel} (Middle x) (Middle y)

export
Asymmetric ty rel => Asymmetric (Bound ty) (BoundedRel {rel}) where
  asymmetric (LTEMiddle yx) (LTEMiddle xy) = asymmetric {rel} xy yx

export
Transitive ty rel => Transitive (Bound ty) (BoundedRel {rel}) where
  transitive {x = Bottom} {z = Middle z} _ _ = LTEBottom
  transitive {x = Bottom} {z = Top} _ _ = LTEBottomTop
  transitive (LTEMiddle xy) (LTEMiddle yz) = LTEMiddle $ transitive xy yz
  transitive {x = Middle x} {z = Top} _ _ = LTETop

public export
data Color = Red | Black

export
Uninhabited (Red = Black) where
  uninhabited Refl impossible

export
Uninhabited (Black = Red) where
  uninhabited Refl impossible

export
eqOrConnex :
  (Connex ty rel, DecEq ty) =>
  (x : ty) ->
  (y : ty) ->
  (dec : Dec (x = y) **
    case dec of
      Yes _ => ()
      No _ => Either (rel x y) (rel y x)
  )
eqOrConnex x y = case x `decEq` y of
  Yes eq => (Yes eq ** ())
  No notEq => (No notEq ** connex {rel} notEq)

public export
data Node : StrictLinearOrder k rel => Color -> Nat -> (0 lower, upper : Bound k) -> Type where
  MkLeaf :
    StrictLinearOrder k rel =>
    {0 lower, upper : Bound k} ->
    {auto ltLowerUpper : BoundedRel {rel} lower upper} ->
    Node {rel} Black Z lower upper
  MkRedNode :
    StrictLinearOrder k rel =>
    {0 lower, upper : Bound k} ->
    (key : k) ->
    (left : Node {rel} Black childHeight lower (Middle key)) ->
    (right : Node {rel} Black childHeight (Middle key) upper) ->
    Node {rel} Red childHeight lower upper
  MkBlackNode :
    StrictLinearOrder k rel =>
    {0 lower, upper : Bound k} ->
    (key : k) ->
    {leftColor, rightColor : Color} ->
    (left : Node {rel} leftColor childHeight lower (Middle key)) ->
    (right : Node {rel} rightColor childHeight (Middle key) upper) ->
    Node {rel} Black (S childHeight) lower upper

export
redToBlack :
  StrictLinearOrder k rel =>
  Node {rel} Red height lower upper ->
  Node {rel} Black (S height) lower upper
redToBlack (MkRedNode key left right) = MkBlackNode key left right

export
nodeBoundsRel :
  StrictLinearOrder k rel =>
  {lower, upper : Bound k} ->
  Node {rel} color height lower upper ->
  BoundedRel {rel} lower upper
nodeBoundsRel (MkLeaf {ltLowerUpper}) = ltLowerUpper
nodeBoundsRel (MkRedNode key left right) =
  transitive (nodeBoundsRel left) (nodeBoundsRel right)
nodeBoundsRel (MkBlackNode key left right) =
  transitive (nodeBoundsRel left) (nodeBoundsRel right)

export
[ShowNode]
  (StrictLinearOrder k rel, Show k) =>
  Show (Node {rel} color height lower upper) where
  show MkLeaf = "[]"
  show (MkRedNode key MkLeaf MkLeaf) = "[\{show key}]"
  show (MkRedNode key MkLeaf right) = "[\{show key} \{show @{ShowNode} right}]"
  show (MkRedNode key left MkLeaf) = "[\{show @{ShowNode} left} \{show key}]"
  show (MkRedNode key left right) = "[\{show @{ShowNode} left} \{show key} \{show @{ShowNode} right}]"
  show (MkBlackNode key MkLeaf MkLeaf) = "[\{show key}]"
  show (MkBlackNode key MkLeaf right) = "[\{show key} \{show @{ShowNode} right}]"
  show (MkBlackNode key left MkLeaf) = "[\{show @{ShowNode} left} \{show key}]"
  show (MkBlackNode key left right) = "[\{show @{ShowNode} left} \{show key} \{show @{ShowNode} right}]"
