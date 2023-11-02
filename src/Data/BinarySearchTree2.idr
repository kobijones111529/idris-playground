module Data.BinarySearchTree2

import Decidable.Equality
import Control.Order
import Data.Nat
import Data.Vect

%default total

public export
data Node : (LinearOrder k rel, DecEq k) => k -> Type -> Type where
  MkNode :
    (LinearOrder k rel, DecEq k) =>
    {key : k} ->
    (val : ty) ->
    Maybe (leftKey : k ** (Node {rel} leftKey ty, rel leftKey key)) ->
    Maybe (rightKey : k ** (Node {rel} rightKey ty, rel key rightKey)) ->
    Node {rel} key ty

public export
data Elem : (LinearOrder k rel, DecEq k) => k -> Node {rel} key ty -> Type where
  Here : (LinearOrder k rel, DecEq k) => {node : Node {rel} key ty} -> Elem key node
  InLeft :
    (LinearOrder k rel, DecEq k) =>
    {auto 0 leftPrf : rel leftKey key} ->
    {node : Node {rel} leftKey ty} ->
    {right : Maybe (rightKey ** (Node {rel} rightKey ty, rel key rightKey))} ->
    Elem {rel} key node ->
    Elem key (MkNode val (Just (leftKey ** (node, leftPrf))) right)
  InRight :
    (LinearOrder k rel, DecEq k) =>
    {auto 0 rightPrf : rel key rightKey} ->
    {node : Node {rel} rightKey ty} ->
    {left : Maybe (leftKey ** (Node {rel} leftKey ty, rel leftKey key))} ->
    Elem {rel} key node ->
    Elem key (MkNode val left (Just (rightKey ** (node, rightPrf))))

-- (LinearOrder k rel, DecEq k) => Uninhabited (Here {rel} {node} = InLeft {rel} {leftPrf} {node} e) where
--   uninhabited = ?h



export
insert' :
  (LinearOrder k rel, DecEq k) =>
  {newKey, rootKey : k} ->
  Node {rel} newKey ty ->
  Node {rel} rootKey ty ->
  Node {rel} rootKey ty
insert' {newKey} {rootKey} node root = case root of
  MkNode val left right =>
    case newKey `decEq` rootKey of
      Yes eq =>
        case left of
          Just (leftKey ** (left, leftPrf)) =>
            MkNode val (Just (leftKey ** (insert' node left, leftPrf))) right
          Nothing => MkNode {key = rootKey} val (Just (newKey ** (node, rewrite eq in reflexive))) right
      No notEq => 
        case connex {rel} notEq of
          Left prf => case left of
            Just (leftKey ** (left, leftPrf)) =>
              MkNode val (Just (leftKey ** (insert' node left, leftPrf))) right
            Nothing => MkNode val (Just (newKey ** (node, prf))) right
          Right prf => case right of
            Just (rightKey ** (right, rightPrf)) =>
              MkNode val left $ Just (rightKey ** (insert' node right, rightPrf))
            Nothing => MkNode val left $ Just (newKey ** (node, prf))

export
get' :
  (LinearOrder k rel, DecEq k) =>
  (key : k) ->
  {rootKey : k} ->
  Node {rel} rootKey ty ->
  Maybe (Node {rel} key ty)
get' key {rootKey} node@(MkNode val left right) = case key `decEq` rootKey of
  Yes eq => rewrite eq in Just node
  No notEq => case connex {rel} notEq of
    Left _ => case left of
      Just (_ ** (left, _)) => get' key left
      Nothing => Nothing
    Right _ =>
      case right of
        Just (_ ** (right, _)) => get' key right
        Nothing => Nothing

export
[ShowNode] (LinearOrder k rel, DecEq k, Show k, Show ty) => Show (Node {k} {rel} key ty) where
  show (MkNode val left right) =
    let
      children =
        case left of
          Just (_ ** (left, _)) => case right of
            Just (_ ** (right, _)) => Just "[\{show @{ShowNode} left}, \{show @{ShowNode} right}]"
            Nothing => Just "[\{show @{ShowNode} left}, _]"
          Nothing => case right of
            Just (_ ** (right, _)) => Just "[_, \{show @{ShowNode} right}]"
            Nothing => Nothing
    in "(\{show key}, \{show val})" ++ maybe "" (" " ++) children
