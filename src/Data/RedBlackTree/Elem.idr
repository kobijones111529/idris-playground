module Data.RedBlackTree.Elem

import public Control.Order.Strict
import Control.Relation.Erased as Erased
import public Data.RedBlackTree.Core
import public Decidable.Equality

%default total

public export
data Elem : StrictLinearOrder k rel => k -> Node {rel} color height lower upper -> Type where
  ThisRed :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} Black childHeight lower key} ->
    {0 right : Node {rel} Black childHeight key upper} ->
    Elem key (MkRedNode key left right)
  ThisBlack :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} leftColor childHeight lower key} ->
    {0 right : Node {rel} rightColor childHeight key upper} ->
    Elem key (MkBlackNode key left right)
  InLeftOfRed :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} Black childHeight lower root} ->
    {0 right : Node {rel} Black childHeight root upper} ->
    Elem key left ->
    Elem key (MkRedNode root left right)
  InLeftOfBlack :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} leftColor childHeight lower root} ->
    {0 right : Node {rel} rightColor childHeight root upper} ->
    Elem key left ->
    Elem key (MkBlackNode root left right)
  InRightOfRed :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} Black childHeight lower root} ->
    {0 right : Node {rel} Black childHeight root upper} ->
    Elem key right ->
    Elem key (MkRedNode root left right)
  InRightOfBlack :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} leftColor childHeight lower root} ->
    {0 right : Node {rel} rightColor childHeight root upper} ->
    Elem key right ->
    Elem key (MkBlackNode root left right)

export
ltNotElem :
  StrictLinearOrder k rel =>
  {key : k} ->
  {0 lower, upper : k} ->
  {node : Node {rel} color height lower upper} ->
  rel key lower ->
  Not (Elem key node)
ltNotElem ltKeyLower (ThisRed {left}) =
  void $ Erased.asymmetric {rel} (nodeBoundsRel left) ltKeyLower
ltNotElem ltKeyLower (ThisBlack {left}) =
  void $ Erased.asymmetric {rel} (nodeBoundsRel left) ltKeyLower
ltNotElem ltKeyLower (InLeftOfRed inLeft) = ltNotElem ltKeyLower inLeft
ltNotElem ltKeyLower (InLeftOfBlack inLeft) = ltNotElem ltKeyLower inLeft
ltNotElem ltKeyLower (InRightOfRed {left} inRight) =
  let
    0 ltKeyLeft = Erased.transitive ltKeyLower (nodeBoundsRel left)
  in void $ ltNotElem ltKeyLeft inRight
ltNotElem ltKeyLower (InRightOfBlack {left} inRight) =
  let
    0 ltKeyLeft = Erased.transitive ltKeyLower (nodeBoundsRel left)
  in void $ ltNotElem ltKeyLeft inRight

export
gtNotElem :
  StrictLinearOrder k rel =>
  {key : k} ->
  {lower, upper : k} ->
  {node : Node {rel} color height lower upper} ->
  rel upper key ->
  Not (Elem key node)
gtNotElem gtKeyUpper (ThisRed {right}) =
  void $ Erased.asymmetric {rel} (nodeBoundsRel right) gtKeyUpper
gtNotElem gtKeyUpper (ThisBlack {right}) =
  void $ Erased.asymmetric {rel} (nodeBoundsRel right) gtKeyUpper
gtNotElem gtKeyUpper (InLeftOfRed {right} inLeft) =
  let
    0 gtKeyRight = Erased.transitive (nodeBoundsRel right) gtKeyUpper
  in void $ gtNotElem gtKeyRight inLeft
gtNotElem gtKeyUpper (InLeftOfBlack {right} inLeft) =
  let
    0 gtKeyRight = Erased.transitive (nodeBoundsRel right) gtKeyUpper
  in void $ gtNotElem gtKeyRight inLeft
gtNotElem gtKeyUpper (InRightOfRed inRight) = gtNotElem gtKeyUpper inRight
gtNotElem gtKeyUpper (InRightOfBlack inRight) = gtNotElem gtKeyUpper inRight
