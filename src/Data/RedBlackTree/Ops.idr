module Data.RedBlackTree.Ops

import public Data.RedBlackTree.Core
import public Data.RedBlackTree.Elem

%default total

export
lookup :
  (StrictLinearOrder k rel, DecEq k) =>
  (key : k) ->
  {lower, upper : Bound k} ->
  (node : Node {rel} color height lower upper) ->
  Dec (Elem key node)
lookup key MkLeaf = No $ \case
  ThisRed impossible
  ThisBlack impossible
  InLeftOfRed _ impossible
  InLeftOfBlack _ impossible
  InRightOfRed _ impossible
  InRightOfBlack _ impossible
lookup key (MkRedNode root left right) = case eqOrConnex {rel} key root of
  (Yes eq ** ()) => Yes $ rewrite sym eq in ThisRed
  (No notEq ** Left lt) => case lookup key left of
    Yes inLeft => Yes $ InLeftOfRed inLeft
    No notInLeft => No $ \case
      ThisRed => irreflexive {rel} lt
      InLeftOfRed inLeft => notInLeft inLeft
      InRightOfRed inRight => ltNotElem (LTEMiddle lt) inRight
  (No notEq ** Right gt) => case lookup key right of
    Yes inRight => Yes $ InRightOfRed inRight
    No notInRight => No $ \case
      ThisRed => irreflexive {rel} gt
      InLeftOfRed inLeft => gtNotElem (LTEMiddle gt) inLeft
      InRightOfRed inRight => notInRight inRight
lookup key (MkBlackNode root left right) = case eqOrConnex {rel} key root of
  (Yes eq ** ()) => Yes $ rewrite sym eq in ThisBlack
  (No notEq ** Left lt) => case lookup key left of
    Yes inLeft => Yes $ InLeftOfBlack inLeft
    No notInLeft => No $ \case
      ThisBlack => irreflexive {rel} lt
      InLeftOfBlack inLeft => notInLeft inLeft
      InRightOfBlack inRight => ltNotElem (LTEMiddle lt) inRight
  (No notEq ** Right gt) => case lookup key right of
    Yes inRight => Yes $ InRightOfBlack inRight
    No notInRight => No $ \case
      ThisBlack => irreflexive {rel} gt
      InLeftOfBlack inLeft => gtNotElem (LTEMiddle gt) inLeft
      InRightOfBlack inRight => notInRight inRight

export
insert :
  (StrictLinearOrder k rel, DecEq k) =>
  (newKey : k) ->
  {0 lower, upper : Bound k} ->
  {auto ltLowerKey : BoundedRel {rel} lower (Middle newKey)} ->
  {auto ltKeyUpper : BoundedRel {rel} (Middle newKey) upper} ->
  Node {rel} Black height lower upper ->
  (color ** Node {rel} color height lower upper)
insert newKey MkLeaf = (Red ** MkRedNode newKey MkLeaf MkLeaf)
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