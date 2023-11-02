module Data.RedBlackTree

import public Control.Order.Strict
import Data.RedBlackTree.Core
import Data.RedBlackTree.Elem
import Data.RedBlackTree.Ops
import public Decidable.Equality

%default total

export
data BinarySearchTree : (k : Type) -> (rel : Rel k) -> StrictLinearOrder k rel => Type where
  Root : StrictLinearOrder k rel => {height : Nat} -> Node {rel} Black height Bottom Top -> BinarySearchTree k rel

export
[ShowBST] StrictLinearOrder k rel => Show k => Show (BinarySearchTree k rel) where
  show (Root node) = show @{ShowNode} node

export
empty : StrictLinearOrder k rel => BinarySearchTree k rel
empty = Root MkLeaf

export
lookup : StrictLinearOrder k rel => DecEq k => k -> BinarySearchTree k rel -> Bool
lookup key (Root node) = case lookup key node of
  Yes _ => True
  No _ => False

export
insert : StrictLinearOrder k rel => DecEq k => k -> BinarySearchTree k rel -> BinarySearchTree k rel
insert key (Root node) = case insert key node of
  (Red ** node) => Root $ redToBlack node
  (Black ** node) => Root node
