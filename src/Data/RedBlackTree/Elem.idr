module Data.RedBlackTree.Elem

import public Control.Order.Strict
import public Data.RedBlackTree.Core
import public Decidable.Equality

%default total

public export
data Elem : StrictLinearOrder k rel => k -> Node {rel} color height lower upper -> Type where
  ThisRed :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} Black childHeight lower (Middle key)} ->
    {0 right : Node {rel} Black childHeight (Middle key) upper} ->
    Elem key (MkRedNode key left right)
  ThisBlack :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} leftColor childHeight lower (Middle key)} ->
    {0 right : Node {rel} rightColor childHeight (Middle key) upper} ->
    Elem key (MkBlackNode key left right)
  InLeftOfRed :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} Black childHeight lower (Middle root)} ->
    {0 right : Node {rel} Black childHeight (Middle root) upper} ->
    Elem key left ->
    Elem key (MkRedNode root left right)
  InLeftOfBlack :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} leftColor childHeight lower (Middle root)} ->
    {0 right : Node {rel} rightColor childHeight (Middle root) upper} ->
    Elem key left ->
    Elem key (MkBlackNode root left right)
  InRightOfRed :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} Black childHeight lower (Middle root)} ->
    {0 right : Node {rel} Black childHeight (Middle root) upper} ->
    Elem key right ->
    Elem key (MkRedNode root left right)
  InRightOfBlack :
    StrictLinearOrder k rel =>
    {0 key : k} ->
    {0 left : Node {rel} leftColor childHeight lower (Middle root)} ->
    {0 right : Node {rel} rightColor childHeight (Middle root) upper} ->
    Elem key right ->
    Elem key (MkBlackNode root left right)

export
ltNotElem :
  StrictLinearOrder k rel =>
  {key : k} ->
  {lower, upper : Bound k} ->
  {node : Node {rel} color height lower upper} ->
  BoundedRel {rel} (Middle key) lower ->
  Not (Elem key node)
ltNotElem ltKeyLower (ThisRed {left}) =
  asymmetric {rel = BoundedRel} (nodeBoundsRel left) ltKeyLower
ltNotElem ltKeyLower (ThisBlack {left}) =
  asymmetric {rel = BoundedRel} (nodeBoundsRel left) ltKeyLower
ltNotElem ltKeyLower (InLeftOfRed inLeft) = ltNotElem ltKeyLower inLeft
ltNotElem ltKeyLower (InLeftOfBlack inLeft) = ltNotElem ltKeyLower inLeft
ltNotElem ltKeyLower (InRightOfRed {left} inRight) =
  let
    ltKeyLeft = transitive ltKeyLower (nodeBoundsRel left)
  in ltNotElem ltKeyLeft inRight
ltNotElem ltKeyLower (InRightOfBlack {left} inRight) =
  let
    ltKeyLeft = transitive ltKeyLower (nodeBoundsRel left)
  in ltNotElem ltKeyLeft inRight

export
gtNotElem :
  StrictLinearOrder k rel =>
  {key : k} ->
  {lower, upper : Bound k} ->
  {node : Node {rel} color height lower upper} ->
  BoundedRel {rel} upper (Middle key) ->
  Not (Elem key node)
gtNotElem gtKeyUpper (ThisRed {right}) =
  asymmetric {rel = BoundedRel} (nodeBoundsRel right) gtKeyUpper
gtNotElem gtKeyUpper (ThisBlack {right}) =
  asymmetric {rel = BoundedRel} (nodeBoundsRel right) gtKeyUpper
gtNotElem gtKeyUpper (InLeftOfRed {right} inLeft) =
  let
    gtKeyRight = transitive (nodeBoundsRel right) gtKeyUpper
  in gtNotElem gtKeyRight inLeft
gtNotElem gtKeyUpper (InLeftOfBlack {right} inLeft) =
  let
    gtKeyRight = transitive (nodeBoundsRel right) gtKeyUpper
  in gtNotElem gtKeyRight inLeft
gtNotElem gtKeyUpper (InRightOfRed inRight) = gtNotElem gtKeyUpper inRight
gtNotElem gtKeyUpper (InRightOfBlack inRight) = gtNotElem gtKeyUpper inRight

