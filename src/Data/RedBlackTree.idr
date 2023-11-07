module Data.RedBlackTree

import public Control.Order.Strict
import Data.RedBlackTree.Core
import Data.RedBlackTree.Elem
import Data.RedBlackTree.Ops
import public Decidable.Equality

%default total

public export
data Bound ty = Bottom | Middle ty | Top

DecEq ty => DecEq (Bound ty) where
  decEq Bottom Bottom = Yes Refl
  decEq Bottom (Middle _) = No $ \case { Refl impossible }
  decEq Bottom Top = No $ \case { Refl impossible }
  decEq (Middle _) Bottom = No $ \case { Refl impossible }
  decEq (Middle x) (Middle y) = case decEq x y of
    Yes eq => Yes $ cong Middle eq
    No notEq => No $ \Refl => notEq Refl
  decEq (Middle x) Top = No $ \case { Refl impossible }
  decEq Top Bottom = No $ \case { Refl impossible }
  decEq Top (Middle x) = No $ \case { Refl impossible }
  decEq Top Top = Yes Refl

public export
data BoundedRel : {0 rel : ty -> ty -> Type} -> Bound ty -> Bound ty -> Type where
  LTEBottomTop : BoundedRel Bottom Top
  LTEBottom : {x : ty} -> BoundedRel Bottom (Middle x)
  LTETop : {x : ty} -> BoundedRel (Middle x) Top
  LTEMiddle : {0 rel : ty -> ty -> Type} -> {x, y : ty} -> rel x y -> BoundedRel {rel} (Middle x) (Middle y)

Irreflexive ty rel => Irreflexive (Bound ty) (BoundedRel {rel}) where
  irreflexive {x = Bottom} _ impossible
  irreflexive {x = (Middle x)} (LTEMiddle lt) = irreflexive {rel} lt
  irreflexive {x = Top} _ impossible

export
Asymmetric ty rel => Asymmetric (Bound ty) (BoundedRel {rel}) where
  asymmetric (LTEMiddle yx) (LTEMiddle xy) = asymmetric {rel} xy yx

export
Transitive ty rel => Transitive (Bound ty) (BoundedRel {rel}) where
  transitive {x = Bottom} {z = Middle z} _ _ = LTEBottom
  transitive {x = Bottom} {z = Top} _ _ = LTEBottomTop
  transitive (LTEMiddle xy) (LTEMiddle yz) = LTEMiddle $ transitive xy yz
  transitive {x = Middle x} {z = Top} _ _ = LTETop

Connex ty rel => Connex (Bound ty) (BoundedRel {rel}) where
  connex {x = Bottom} {y = Bottom} notEq = void $ notEq Refl
  connex {x = Bottom} {y = (Middle x)} notEq = Left LTEBottom
  connex {x = Bottom} {y = Top} notEq = Left LTEBottomTop
  connex {x = (Middle x)} {y = Bottom} notEq = Right LTEBottom
  connex {x = (Middle x)} {y = (Middle y)} notEq =
    let
      xyNotEq = \eq => notEq $ cong Middle eq
    in case connex {rel} xyNotEq of
      (Left xy) => Left $ LTEMiddle xy
      (Right yx) => Right $ LTEMiddle yx
  connex {x = (Middle x)} {y = Top} notEq = Left LTETop
  connex {x = Top} {y = Bottom} notEq = Right LTEBottomTop
  connex {x = Top} {y = (Middle x)} notEq = Right LTETop
  connex {x = Top} {y = Top} notEq = void $ notEq Refl

StrictLinearOrder ty rel => StrictLinearOrder (Bound ty) (BoundedRel {rel}) where

export
data BinarySearchTree : (k : Type) -> (rel : Rel k) -> StrictLinearOrder k rel => Type where
  Root : StrictLinearOrder k rel => {height : Nat} -> Node {rel = BoundedRel {rel}} Black height Bottom Top -> BinarySearchTree k rel

export
[ShowBST] StrictLinearOrder k rel => Show k => Show (BinarySearchTree k rel) where
  show (Root node) = showNode node
  where
    showBound : Show ty => Bound ty -> String
    showBound Bottom = "⊥"
    showBound (Middle x) = show x
    showBound Top = "⊤"

    showNode : Node {rel = BoundedRel {rel}} color height lower upper -> String
    showNode MkLeaf = "[]"
    showNode (MkRedNode key MkLeaf MkLeaf) = "[\{showBound key}]"
    showNode (MkRedNode key MkLeaf right) = "[\{showBound key} \{showNode right}]"
    showNode (MkRedNode key left MkLeaf) = "[\{showNode left} \{showBound key}]"
    showNode (MkRedNode key left right) = "[\{showNode left} \{showBound key} \{showNode right}]"
    showNode (MkBlackNode key MkLeaf MkLeaf) = "[\{showBound key}]"
    showNode (MkBlackNode key MkLeaf right) = "[\{showBound key} \{showNode right}]"
    showNode (MkBlackNode key left MkLeaf) = "[\{showNode left} \{showBound key}]"
    showNode (MkBlackNode key left right) = "[\{showNode left} \{showBound key} \{showNode right}]"

export
empty : StrictLinearOrder k rel => BinarySearchTree k rel
empty = Root MkLeaf

export
lookup : StrictLinearOrder k rel => DecEq k => k -> BinarySearchTree k rel -> Bool
lookup key (Root node) = case lookup (Middle key) node of
  Yes _ => True
  No _ => False

export
insert : StrictLinearOrder k rel => DecEq k => k -> BinarySearchTree k rel -> BinarySearchTree k rel
insert key (Root node) = case insert (Middle key) node of
  (Red ** node) => Root $ redToBlack node
  (Black ** node) => Root node
