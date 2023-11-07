module Data.RedBlackTree.Core

import public Control.Order.Strict
import public Decidable.Equality

%default total

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
data Node : StrictLinearOrder k rel => Color -> Nat -> (0 lower, upper : k) -> Type where
  MkLeaf :
    StrictLinearOrder k rel =>
    {0 lower, upper : k} ->
    {auto ltLowerUpper : rel lower upper} ->
    Node {rel} Black Z lower upper
  MkRedNode :
    StrictLinearOrder k rel =>
    {0 lower, upper : k} ->
    (key : k) ->
    (left : Node {rel} Black childHeight lower key) ->
    (right : Node {rel} Black childHeight key upper) ->
    Node {rel} Red childHeight lower upper
  MkBlackNode :
    StrictLinearOrder k rel =>
    {0 lower, upper : k} ->
    (key : k) ->
    {leftColor, rightColor : Color} ->
    (left : Node {rel} leftColor childHeight lower key) ->
    (right : Node {rel} rightColor childHeight key upper) ->
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
  {lower, upper : k} ->
  Node {rel} color height lower upper ->
  rel lower upper
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
