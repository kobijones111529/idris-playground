module Data.RedBlackTree.Ops

import public Data.RedBlackTree.Core
import public Data.RedBlackTree.Elem
import Decidable.Ordering

%default total

export
lookup :
  (StrictLinearOrder k rel, DecEq k) =>
  (key : k) ->
  {0 lower, upper : k} ->
  (node : Node {rel} color height lower upper) ->
  Dec (Elem key node)
lookup key MkLeaf = No $ \case
  ThisRed impossible
  ThisBlack impossible
  InLeftOfRed _ impossible
  InLeftOfBlack _ impossible
  InRightOfRed _ impossible
  InRightOfBlack _ impossible
lookup key (MkRedNode root left right) =
  case decOrd {rel} key root of
    EQ eq => Yes $ rewrite sym eq in ThisRed
    LT lt => case lookup key left of
      Yes inLeft => Yes $ InLeftOfRed inLeft
      No notInLeft => No $ \case
        ThisRed => irreflexive {rel} lt
        InLeftOfRed inLeft => notInLeft inLeft
        InRightOfRed inRight => void $ ltNotElem lt inRight
    GT gt => case lookup key right of
      Yes inRight => Yes $ InRightOfRed inRight
      No notInRight => No $ \case
        ThisRed => irreflexive {rel} gt
        InLeftOfRed inLeft => void $ gtNotElem gt inLeft
        InRightOfRed inRight => notInRight inRight
lookup key (MkBlackNode root left right) =
  case decOrd {rel} key root of
    EQ eq => Yes $ rewrite sym eq in ThisBlack
    LT lt => case lookup key left of
      Yes inLeft => Yes $ InLeftOfBlack inLeft
      No notInLeft => No $ \case
        ThisBlack => irreflexive {rel} lt
        InLeftOfBlack inLeft => notInLeft inLeft
        InRightOfBlack inRight => ltNotElem lt inRight
    GT gt => case lookup key right of
      Yes inRight => Yes $ InRightOfBlack inRight
      No notInRight => No $ \case
        ThisBlack => irreflexive {rel} gt
        InLeftOfBlack inLeft => void $ gtNotElem gt inLeft
        InRightOfBlack inRight => notInRight inRight

mutual
  export
  insert :
    (StrictLinearOrder k rel, DecEq k) =>
    (newKey : k) ->
    {auto 0 ltLowerKey : rel lower newKey} ->
    {auto 0 ltKeyUpper : rel newKey upper} ->
    Node {rel} Black height lower upper ->
    (color ** Node {rel} color height lower upper)
  insert newKey node =
    case node of
      MkLeaf => (Red ** MkRedNode newKey MkLeaf MkLeaf)
      MkBlackNode {childHeight} {leftColor} {rightColor} key left right =>
        case decOrd {rel} newKey key of
          EQ _ => (Black ** MkBlackNode key left right)
          LT _ => insertLeft newKey key left right
            -- case leftColor of
            --   Red =>
            --     let MkRedNode leftKey leftLeft leftRight = left
            --     in case decOrd {rel} newKey leftKey of
            --       EQ _ => (Black ** MkBlackNode key left right)
            --       LT _ =>
            --         -- let (_ ** leftLeft) = insert newKey leftLeft
            --         -- in insertLeftLeft leftKey leftLeft leftRight
            --         case insert newKey leftLeft of
            --           (Red ** leftLeft) => case rightColor of
            --             Red =>
            --               (Red **
            --                 MkRedNode
            --                   key
            --                   (MkBlackNode leftKey leftLeft leftRight)
            --                   (redToBlack right)
            --               )
            --             Black =>
            --               (Black **
            --                 MkBlackNode leftKey leftLeft (MkRedNode key leftRight right)
            --               )
            --           (Black ** leftLeft) =>
            --             (Black ** MkBlackNode key (MkRedNode leftKey leftLeft leftRight) right)
            --       GT _ => case insert newKey leftRight of
            --         (Red ** leftRight@(MkRedNode leftRightKey leftRightLeft leftRightRight)) => case rightColor of
            --           Red =>
            --             (Red **
            --               MkRedNode
            --                 key
            --                 (MkBlackNode leftKey leftLeft leftRight)
            --                 (redToBlack right)
            --             )
            --           Black =>
            --             (Black **
            --               MkBlackNode
            --                 leftRightKey
            --                 (MkRedNode leftKey leftLeft leftRightLeft)
            --                 (MkRedNode key leftRightRight right)
            --             )
            --         (Black ** leftRight) => (Black ** MkBlackNode key (MkRedNode leftKey leftLeft leftRight) right)
            --   Black => case insert newKey left of
            --     (Red ** left) => (Black ** MkBlackNode key left right)
            --     (Black ** left) => (Black ** MkBlackNode key left right)
          GT _ => insertRight newKey key left right

  insertLeft :
    (StrictLinearOrder k rel, DecEq k) =>
    (newKey : k) ->
    (key : k) ->
    {auto 0 ltLowerNewKey : rel lower newKey} ->
    {auto 0 ltNewKeyKey : rel newKey key} ->
    {leftColor, rightColor : Color} ->
    Node {rel} leftColor height lower key ->
    Node {rel} rightColor height key upper ->
    (color ** Node {rel} color (S height) lower upper)
  insertLeft newKey key left right =
    case leftColor of
      Red =>
        let MkRedNode leftKey leftLeft leftRight = left
        in case decOrd {rel} newKey leftKey of
          EQ _ => (Black ** MkBlackNode key left right)
          LT _ => helpLeft leftKey leftLeft leftRight
          GT _ => helpRight leftKey leftLeft leftRight
      Black =>
        let (_ ** left) = insert newKey left
        in (Black ** MkBlackNode key left right)

    where
      helpLeft :
        (leftKey : k) ->
        {auto 0 _ : rel newKey leftKey} ->
        Node {rel} Black height lower leftKey ->
        Node {rel} Black height leftKey key ->
        (color ** Node {rel} color (S height) lower upper)
      helpLeft leftKey leftLeft leftRight =
        case insert newKey leftLeft of
          (Red ** leftLeft) =>
            case rightColor of
              Red =>
                let left = MkBlackNode leftKey leftLeft leftRight
                in (Red ** MkRedNode key left $ redToBlack right)
              Black =>
                let right = MkRedNode key leftRight right
                in (Black ** MkBlackNode leftKey leftLeft right)
          (Black ** leftLeft) =>
            let left = MkRedNode leftKey leftLeft leftRight
            in (Black ** MkBlackNode key left right)

      helpRight :
        (leftKey : k) ->
        {auto 0 _ : rel leftKey newKey} ->
        Node {rel} Black height lower leftKey ->
        Node {rel} Black height leftKey key ->
        (color ** Node {rel} color (S height) lower upper)
      helpRight leftKey leftLeft leftRight =
        case insert newKey leftRight of
          (Red ** leftRight) =>
            case rightColor of
              Red =>
                let left = MkBlackNode leftKey leftLeft leftRight
                in (Red ** MkRedNode key left (redToBlack right))
              Black =>
                let
                  MkRedNode leftRightKey leftRightLeft leftRightRight = leftRight
                  left = MkRedNode leftKey leftLeft leftRightLeft
                  right = MkRedNode key leftRightRight right
                in (Black ** MkBlackNode leftRightKey left right)
          (Black ** leftRight) =>
            let left = MkRedNode leftKey leftLeft leftRight
            in (Black ** MkBlackNode key left right)

  insertRight :
    (StrictLinearOrder k rel, DecEq k) =>
    (newKey : k) ->
    (key : k) ->
    {auto 0 ltKeyNewKey : rel key newKey} ->
    {auto 0 ltNewKeyUpper : rel newKey upper} ->
    {leftColor, rightColor : Color} ->
    Node {rel} leftColor height lower key ->
    Node {rel} rightColor height key upper ->
    (color ** Node {rel} color (S height) lower upper)
  insertRight newKey key left right =
    case rightColor of
      Red =>
        let MkRedNode rightKey rightLeft rightRight = right
        in case decOrd {rel} newKey rightKey of
          EQ _ => (Black ** MkBlackNode key left right)
          LT _ => helpLeft rightKey rightLeft rightRight
          GT _ => helpRight rightKey rightLeft rightRight
      Black =>
        let (_ ** right) = insert newKey right
        in (Black ** MkBlackNode key left right)

    where
      helpLeft :
        (rightKey : k) ->
        {auto 0 _ : rel newKey rightKey} ->
        Node {rel} Black height key rightKey ->
        Node {rel} Black height rightKey upper ->
        (color ** Node {rel} color (S height) lower upper)
      helpLeft rightKey rightLeft rightRight =
        case insert newKey rightLeft of
          (Red ** rightLeft) =>
            case leftColor of
              Red =>
                let right = MkBlackNode rightKey rightLeft rightRight
                in (Red ** MkRedNode key (redToBlack left) right)
              Black =>
                let
                  MkRedNode rightLeftKey rightLeftLeft rightLeftRight = rightLeft
                  left = MkRedNode key left rightLeftLeft
                  right = MkRedNode rightKey rightLeftRight rightRight
                in (Black ** MkBlackNode rightLeftKey left right)
          (Black ** rightLeft) =>
            let right = MkRedNode rightKey rightLeft rightRight
            in (Black ** MkBlackNode key left right)

      helpRight :
        (rightKey : k) ->
        {auto 0 _ : rel rightKey newKey} ->
        Node {rel} Black height key rightKey ->
        Node {rel} Black height rightKey upper ->
        (color ** Node {rel} color (S height) lower upper)
      helpRight rightKey rightLeft rightRight =
        case insert newKey rightRight of
          (Red ** rightRight) =>
            case leftColor of
              Red =>
                let right = MkBlackNode rightKey rightLeft rightRight
                in (Red ** MkRedNode key (redToBlack left) right)
              Black =>
                let left = MkRedNode key left rightLeft
                in (Black ** MkBlackNode rightKey left rightRight)
          (Black ** rightRight) =>
            let right = MkRedNode rightKey rightLeft rightRight
            in (Black ** MkBlackNode key left right)
