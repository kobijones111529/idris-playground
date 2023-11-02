module Data.BinarySearchTree

import Control.Order.Strict
import Decidable.Equality

%default total

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
data Node : StrictLinearOrder k rel => (0 lower, upper : Bound k) -> Type where
  MkLeaf :
    StrictLinearOrder k rel =>
    {lower, upper : Bound k} ->
    {auto ltLowerUpper : BoundedRel {rel} lower upper} ->
    Node {rel} lower upper
  MkNode :
    StrictLinearOrder k rel =>
    {lower, upper : Bound k} ->
    (key : k) ->
    (left : Node {rel} lower (Middle key)) ->
    (right : Node {rel} (Middle key) upper) ->
    Node {rel} lower upper

nodeBoundsRel : StrictLinearOrder k rel => Node {rel} lower upper -> BoundedRel {rel} lower upper
nodeBoundsRel (MkLeaf {ltLowerUpper}) = ltLowerUpper
nodeBoundsRel (MkNode key left right) =
  transitive (nodeBoundsRel left) (nodeBoundsRel right)

data Elem : StrictLinearOrder k rel => k -> Node {rel} lower upper -> Type where
  Here :
    StrictLinearOrder k rel =>
    {left : Node {rel} lower (Middle key)} ->
    {right : Node {rel} (Middle key) upper} ->
    Elem key (MkNode key left right)
  InLeft :
    StrictLinearOrder k rel =>
    {left : Node {rel} lower (Middle root)} ->
    {right : Node {rel} (Middle root) upper} ->
    Elem key left ->
    Elem key (MkNode root left right)
  InRight :
    StrictLinearOrder k rel =>
    {left : Node {rel} lower (Middle root)} ->
    {right : Node {rel} (Middle root) upper} ->
    Elem key right ->
    Elem key (MkNode root left right)

ltNotElem :
  StrictLinearOrder k rel =>
  {key : k} ->
  {node : Node {rel} lower upper} ->
  BoundedRel {rel} (Middle key) lower ->
  Not (Elem key node)
ltNotElem ltKeyLower (Here {left}) =
  asymmetric {rel = BoundedRel} (nodeBoundsRel left) ltKeyLower
ltNotElem ltKeyLower (InLeft inLeft) = ltNotElem ltKeyLower inLeft
ltNotElem ltKeyLower (InRight {left} inRight) =
  let
    ltKeyLeft = transitive ltKeyLower (nodeBoundsRel left)
  in ltNotElem ltKeyLeft inRight

gtNotElem :
  StrictLinearOrder k rel =>
  {key : k} ->
  {node : Node {rel} lower upper} ->
  BoundedRel {rel} upper (Middle key) ->
  Not (Elem key node)
gtNotElem gtKeyUpper (Here {right}) =
  asymmetric {rel = BoundedRel} (nodeBoundsRel right) gtKeyUpper
gtNotElem gtKeyUpper (InLeft {right} inLeft) =
  let
    gtKeyRight = transitive (nodeBoundsRel right) gtKeyUpper
  in gtNotElem gtKeyRight inLeft
gtNotElem gtKeyUpper (InRight inRight) = gtNotElem gtKeyUpper inRight

lookup' :
  (StrictLinearOrder k rel, DecEq k) =>
  (key : k) ->
  (node : Node {rel} lower upper) ->
  Dec (Elem key node)
lookup' key MkLeaf = No $ \case
  Here impossible
  (InLeft _) impossible
  (InRight _) impossible
lookup' key (MkNode key' left right) = case eqOrConnex {rel} key key' of
  (Yes eq ** ()) => Yes $ rewrite sym eq in Here
  (No _ ** Left lt) => case lookup' key left of
    Yes inLeft => Yes $ InLeft inLeft
    No notInLeft => No $ \case
      Here => irreflexive {rel} lt
      InLeft inLeft => notInLeft inLeft
      InRight inRight => ltNotElem (LTEMiddle {rel} lt) inRight
  (No _ ** Right gt) => case lookup' key right of
    Yes inRight => Yes $ InRight inRight
    No notInRight => No $ \case
      Here => irreflexive {rel} gt
      InLeft inLeft => gtNotElem (LTEMiddle {rel} gt) inLeft
      InRight inRight => notInRight inRight

export
insert' :
  (StrictLinearOrder k rel, DecEq k) =>
  (newKey : k) ->
  {0 lower : Bound k} ->
  {0 upper : Bound k} ->
  {auto lowerPrf : BoundedRel {rel} lower (Middle newKey)} ->
  {auto upperPrf : BoundedRel {rel} (Middle newKey) upper} ->
  Node {rel} {lower} {upper} ->
  Node {rel} {lower} {upper}
insert' {lowerPrf} {upperPrf} newKey MkLeaf = MkNode newKey MkLeaf MkLeaf
insert' {rel} newKey (MkNode key left right) =
  case eqOrConnex {rel} newKey key of
    (Yes _ ** ()) => MkNode {rel} key left right
    (No _ ** Left lt) =>
      MkNode {rel}
        key
        (insert' newKey left {lowerPrf} {upperPrf = LTEMiddle lt})
        right
    (No _ ** Right gt) =>
      MkNode {rel}
        key
        left
        (insert' newKey right {lowerPrf = LTEMiddle gt} {upperPrf})

export
[ShowNode] (StrictLinearOrder k rel, Show k) => Show (Node {rel} lower upper) where
  show MkLeaf = "[]"
  show (MkNode key MkLeaf MkLeaf) = "[\{show key}]"
  show (MkNode key MkLeaf right) = "[\{show key} \{show @{ShowNode} right}]"
  show (MkNode key left MkLeaf) = "[\{show @{ShowNode} left} \{show key}]"
  show (MkNode key left right) = "[\{show @{ShowNode} left} \{show key} \{show @{ShowNode} right}]"

export
BinarySearchTree : (k : Type) -> (rel : Rel k) -> StrictLinearOrder k rel => Type
BinarySearchTree _ rel = Node {rel} Bottom Top

export
[ShowBST] (StrictLinearOrder k rel, Show k) => Show (BinarySearchTree k rel) where
  show node = show @{ShowNode} node

export
empty : StrictLinearOrder k rel => BinarySearchTree k rel
empty = MkLeaf

export
lookup : (StrictLinearOrder k rel, DecEq k) => k -> BinarySearchTree k rel -> Bool
lookup key node = case lookup' key node of
  Yes _ => True
  No _ => False

export
insert : (StrictLinearOrder k rel, DecEq k) => k -> BinarySearchTree k rel -> BinarySearchTree k rel
insert key node = insert' key node
