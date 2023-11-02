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

Asymmetric ty rel => Asymmetric (Bound ty) (BoundedRel {rel}) where
  asymmetric (LTEMiddle yx) (LTEMiddle xy) = asymmetric {rel} xy yx

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

public export
data Node : StrictLinearOrder k rel => Color -> Nat -> (0 lower, upper : Bound k) -> Type where
  MkLeaf :
    StrictLinearOrder k rel =>
    {lower, upper : Bound k} ->
    {auto ltLowerUpper : BoundedRel {rel} lower upper} ->
    Node {rel} Black Z lower upper
  MkRedNode :
    StrictLinearOrder k rel =>
    {lower, upper : Bound k} ->
    (key : k) ->
    (left : Node {rel} Black childHeight lower (Middle key)) ->
    (right : Node {rel} Black childHeight (Middle key) upper) ->
    Node {rel} Red childHeight lower upper
  MkBlackNode :
    StrictLinearOrder k rel =>
    {lower, upper : Bound k} ->
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
nodeBoundsRel : StrictLinearOrder k rel => Node {rel} color height lower upper -> BoundedRel {rel} lower upper
nodeBoundsRel (MkLeaf {ltLowerUpper}) = ltLowerUpper
nodeBoundsRel (MkRedNode key left right) =
  transitive (nodeBoundsRel left) (nodeBoundsRel right)
nodeBoundsRel (MkBlackNode key left right) =
  transitive (nodeBoundsRel left) (nodeBoundsRel right)

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

export
insert :
  (StrictLinearOrder k rel, DecEq k) =>
  (newKey : k) ->
  {auto ltLowerKey : BoundedRel {rel} lower (Middle newKey)} ->
  {auto ltKeyUpper : BoundedRel {rel} (Middle newKey) upper} ->
  Node {rel} Black height lower upper ->
  (color ** Node {rel} color height lower upper)
insert {ltKeyUpper} newKey MkLeaf = (Red ** MkRedNode newKey MkLeaf MkLeaf)
insert
  {height = S childHeight}
  newKey
  (MkBlackNode {childHeight} {leftColor} {rightColor} key left right) =
  case eqOrConnex {rel} newKey key of
    (Yes _ ** ()) => (Black ** MkBlackNode key left right)
    (No notEq ** Left lt) => case leftColor of
      Red =>
        let MkRedNode leftKey leftLeft leftRight = left
        in case eqOrConnex {rel} newKey leftKey of
          (Yes _ ** ()) => (Black ** MkBlackNode key left right)
          (No _ ** Left lt') => case insert newKey leftLeft of
            (Red ** leftLeft) => case rightColor of
              Red =>
                (Red **
                  MkRedNode
                    key
                    (MkBlackNode leftKey leftLeft leftRight)
                    (redToBlack right)
                )
              Black =>
                (Black **
                  MkBlackNode leftKey leftLeft (MkRedNode key leftRight right)
                )
            (Black ** leftLeft) =>
              (Black ** MkBlackNode key (MkRedNode leftKey leftLeft leftRight) right)
          (No _ ** Right gt') => case insert newKey leftRight of
            (Red ** leftRight@(MkRedNode leftRightKey leftRightLeft leftRightRight)) => case rightColor of
              Red =>
                (Red **
                  MkRedNode
                    key
                    (MkBlackNode leftKey leftLeft leftRight)
                    (redToBlack right)
                )
              Black =>
                (Black **
                  MkBlackNode
                    leftRightKey
                    (MkRedNode leftKey leftLeft leftRightLeft)
                    (MkRedNode key leftRightRight right)
                )
            (Black ** leftRight) => (Black ** MkBlackNode key (MkRedNode leftKey leftLeft leftRight) right)
      Black => case insert newKey left of
        (Red ** left) => (Black ** MkBlackNode key left right)
        (Black ** left) => (Black ** MkBlackNode key left right)
    (No notEq ** Right gt) => case rightColor of
      Red =>
        let MkRedNode rightKey rightLeft rightRight = right
        in case eqOrConnex {rel} newKey rightKey of
          (Yes _ ** ()) => (Black ** MkBlackNode key left right)
          (No _ ** Left lt') => case insert newKey rightLeft of
            (Red ** rightLeft@(MkRedNode rightLeftKey rightLeftLeft rightLeftRight)) => case leftColor of
              Red =>
                (Red **
                  MkRedNode
                    key
                    (redToBlack left)
                    (MkBlackNode rightKey rightLeft rightRight)
                )
              Black =>
                (Black **
                  MkBlackNode
                    rightLeftKey
                    (MkRedNode key left rightLeftLeft)
                    (MkRedNode rightKey rightLeftRight rightRight)
                )
            (Black ** rightLeft) => (Black ** MkBlackNode key left (MkRedNode rightKey rightLeft rightRight))
          (No _ ** Right gt') => case insert newKey rightRight of
            (Red ** rightRight) => case leftColor of
              Red =>
                (Red **
                  MkRedNode
                    key
                    (redToBlack left)
                    (MkBlackNode rightKey rightLeft rightRight)
                )
              Black =>
                (Black **
                  MkBlackNode
                    rightKey (MkRedNode key left rightLeft) rightRight
                )
            (Black ** rightRight) =>
              (Black **
                MkBlackNode key left (MkRedNode rightKey rightLeft rightRight)
              )
      Black => case insert newKey right of
        (Red ** right) => (Black ** MkBlackNode key left right)
        (Black ** right) => (Black ** MkBlackNode key left right)

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
