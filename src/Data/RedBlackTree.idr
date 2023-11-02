module Data.RedBlackTree

import Control.Order
import Control.Order.Strict
import Control.Relation
import Control.Relation.Irreflexive
import Decidable.Equality

%default total

-- TODO: implement min/max proofs

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

data Color = Red | Black

heightOf : Color -> Nat
heightOf Red = 0
heightOf Black = 1

Uninhabited (Red = Black) where
  uninhabited Refl impossible

Uninhabited (Black = Red) where
  uninhabited Refl impossible

mutual
  -- interface BlackHeight ty where
  --   blackHeight : ty -> Nat

  -- (BlackHeight left, BlackHeight right) => BlackHeight (Either left right) where
  --   blackHeight (Left x) = blackHeight x
  --   blackHeight (Right x) = blackHeight x

  data Leaf :
    StrictLinearOrder k rel =>
    Color ->
    {height : Nat} ->
    k ->
    ty ->
    Type where
    MkLeaf :
      StrictLinearOrder k rel =>
      (col : Color) ->
      (key : k) ->
      (val : ty) ->
      Leaf {rel} col {height = heightOf col} key ty

  -- (StrictLinearOrder k rel) => BlackHeight (Leaf {rel} col key ty) where
  --   blackHeight (MkLeaf Red _ _) = 0
  --   blackHeight (MkLeaf Black _ _) = 1

  data Branch1 :
    StrictLinearOrder k rel =>
    {height : Nat} ->
    k ->
    ty ->
    Type where
    MkBranch1 :
      StrictLinearOrder k rel =>
      (key : k) ->
      (val : ty) ->
      {childHeight : Nat} ->
      {childKey : k} ->
      {auto childRel : Not (childKey = key)} ->
      (child : Leaf {rel} {height = childHeight} Red childKey ty) ->
      Branch1 {rel} {height = S childHeight} key ty

  -- (StrictLinearOrder k rel) => BlackHeight (Branch1 {rel} key ty) where
  --   blackHeight (MkBranch1 _ _ child) = S $ blackHeight child

  branch2Height : Color -> Nat -> Nat
  branch2Height Red childHeight = childHeight
  branch2Height Black childHeight = S childHeight

  data Branch2 :
    StrictLinearOrder k rel =>
    Color ->
    {height : Nat} ->
    {min : k} ->
    {max : k} ->
    k ->
    ty ->
    Type where
    MkBranch2 :
      StrictLinearOrder k rel =>
      (col : Color) ->
      (key : k) ->
      (val : ty) ->
      {childHeight : Nat} ->
      {leftCol : Color} ->
      {leftKey : k} ->
      {auto 0 leftPrf : leftKey `rel` key} ->
      {rightCol : Color} ->
      {rightKey : k} ->
      {auto 0 rightPrf : key `rel` rightKey} ->
      (left : case col of
        Red => Either (Leaf {rel} Black {height = childHeight} leftKey ty) (Either (Branch1 {rel} {height = childHeight} leftKey ty) (Branch2 {rel} Black {height = childHeight} leftKey ty))
        Black => Either (Leaf {rel} leftCol {height = childHeight} leftKey ty) (Either (Branch1 {rel} {height = childHeight} leftKey ty) (Branch2 {rel} leftCol {height = childHeight} leftKey ty))
      ) ->
      (right : case col of
        Red => Either (Leaf {rel} Black {height = childHeight} rightKey ty) (Either (Branch1 {rel} {height = childHeight} rightKey ty) (Branch2 {rel} Black {height = childHeight} rightKey ty))
        Black => Either (Leaf {rel} rightCol {height = childHeight} rightKey ty) (Either (Branch1 {rel} {height = childHeight} rightKey ty) (Branch2 {rel} rightCol {height = childHeight} rightKey ty))
      ) ->
      Branch2 {rel} col {height = branch2Height col childHeight} key ty

  -- {col : Color} -> (StrictLinearOrder k rel) => BlackHeight (Branch2 {rel} col key ty) where
  --   blackHeight (MkBranch2 Red _ _ {childHeight} left right) = childHeight
  --   blackHeight (MkBranch2 Black _ _ {childHeight} left right) = S childHeight

  data Node :
    StrictLinearOrder k rel =>
    k ->
    ty ->
    Type where
    LeafNode :
      (StrictLinearOrder k rel) =>
      Leaf {rel} col key ty ->
      Node {rel} key ty
    Branch1Node :
      (StrictLinearOrder k rel) =>
      Branch1 {rel} key ty ->
      Node {rel} key ty
    Branch2Node :
      (StrictLinearOrder k rel) =>
      Branch2 {rel} col key ty ->
      Node {rel} key ty

  insertLeaf :
    (StrictLinearOrder k rel, DecEq k) =>
    {replace : Bool} ->
    (newKey : k) ->
    (newVal : ty) ->
    {col : Color} ->
    {height : Nat} ->
    Leaf {rel} col {height} key ty ->
    if replace
      then Either (ty, Leaf {rel} col {height} newKey ty) (Branch1 {rel} {height = 1} key ty)
      else Maybe (Branch1 {rel} {height = 1} key ty)
  insertLeaf newKey newVal root @(MkLeaf col key val) =
    case newKey `decEq` key of
      Yes eq => if replace
        then Left $ (val, MkLeaf col newKey newVal)
        else Nothing
      No notEq =>
        let
          res = MkBranch1
            {rel}
            key
            val
            (MkLeaf Red newKey newVal)
        in if replace
          then Right res
          else Just res

  insertBranch1 :
    (StrictLinearOrder k rel, DecEq k) =>
    {replace : Bool} ->
    (newKey : k) ->
    (newVal : ty) ->
    {height : Nat} ->
    {key : k} ->
    Branch1 {rel} {height} key ty ->
    if replace
      then Either (ty, Branch1 {rel} {height} key ty) (rootKey ** Branch2 {rel} Black {height} rootKey ty)
      else Maybe (rootKey ** Branch2 {rel} Black {height} rootKey ty)
  insertBranch1 {replace} newKey newVal (MkBranch1 key val {childRel} child @(MkLeaf Red childKey childVal)) =
    case eqOrConnex {rel} newKey key of
      (Yes eq ** ()) => if replace
        then
          let
            childRel = rewrite eq in childRel
            res = MkBranch1 {childRel} newKey newVal child
          in Left (val, rewrite sym eq in res)
        else Nothing
      (No _ ** Left _) => case connex {rel} childRel of
        Left _ => case newKey `decEq` childKey of
          Yes _ => if replace
            then
              let res = MkBranch1 key val $ MkLeaf Red newKey newVal
              in Left (childVal, res)
            else Nothing
          No notEq' => case connex {rel} notEq' of
            Left _ =>
              let
                res = MkBranch2 Black childKey childVal
                  (Left $ MkLeaf Red newKey newVal)
                  (Left $ MkLeaf Red key val)
              in if replace
                then Right (childKey ** res)
                else Just (childKey ** res)
            Right _ =>
              let
                res = MkBranch2 Black newKey newVal
                  (Left $ MkLeaf Red childKey childVal)
                  (Left $ MkLeaf Red key val)
              in if replace
                then Right (newKey ** res)
                else Just (newKey ** res)
        Right _ =>
          let
            res = MkBranch2 Black key val
              (Left $ MkLeaf Red newKey newVal)
              (Left $ MkLeaf Red childKey childVal)
          in if replace
            then Right (key ** res)
            else Just (key ** res)
      (No _ ** Right _) => case connex {rel} childRel of
          Left _ =>
            let
              res = MkBranch2 Black key val
                (Left $ MkLeaf Red childKey childVal)
                (Left $ MkLeaf Red newKey newVal)
            in if replace
              then Right (key ** res)
              else Just (key ** res)
          Right _ => case eqOrConnex {rel} newKey childKey of
            (Yes _ ** ()) => if replace
              then Left (childVal, MkBranch1 key val $ MkLeaf Red newKey newVal)
              else Nothing
            (No _ ** Left _) =>
              let
                res = MkBranch2 Black newKey newVal
                  (Left $ MkLeaf Red key val)
                  (Left $ MkLeaf Red childKey childVal)
              in if replace
                then Right (newKey ** res)
                else Just (newKey ** res)
            (No _ ** Right _) =>
              let
                res = MkBranch2 Black childKey childVal
                  (Left $ MkLeaf Red key val)
                  (Left $ MkLeaf Red newKey newVal)
              in if replace
                then Right (childKey ** res)
                else Just (childKey ** res)

  insertBranch2 :
    (StrictLinearOrder k rel, DecEq k) =>
    {replace : Bool} ->
    (newKey : k) ->
    (newVal : ty) ->
    {height : Nat} ->
    {key : k} ->
    Branch2 {rel} Black {height} key ty ->
    if replace
      then Either (ty, Branch2 {rel} Black {height} key ty) (info : (Color, k) ** Branch2 {rel} (Builtin.fst info) {height} (Builtin.snd info) ty)
      else Maybe (info : (Color, k) ** Branch2 {rel} (Builtin.fst info) {height} (Builtin.snd info) ty)
  insertBranch2 newKey newVal (MkBranch2 Black key val {childHeight} {leftPrf} {leftCol} {rightCol} {rightPrf} left right) =
    case eqOrConnex {rel} newKey key of
      (Yes eq ** ()) =>
        if replace
          then
            let
              0 leftPrf = rewrite eq in leftPrf
              0 rightPrf = rewrite eq in rightPrf
              res = MkBranch2 Black newKey newVal {leftPrf} {rightPrf} left right
            in Left (val, rewrite sym eq in res)
          else Nothing
      (No _ ** Left _) => case left of
        Left left @(MkLeaf Red leftKey leftVal) =>
          let
            newLeft = insertLeaf {replace} newKey newVal left
          in if replace
            then case newLeft of
              Left (replaced, left) => Left (
                  replaced,
                  MkBranch2 Black key val
                    (Left left)
                    right
                )
              Right (MkBranch1 leftKey leftVal child) =>
                Right ((Red, key) ** MkBranch2 Red key val
                  (Right . Left $ MkBranch1 leftKey leftVal child)
                  (case right of
                    Left (MkLeaf Red rightKey rightVal) => Left $ MkLeaf Black rightKey rightVal
                    Left (MkLeaf Black _ _) impossible
                  )
                )
            else case newLeft of
              Just (MkBranch1 leftKey leftVal child) =>
                Just ((Red, key) ** MkBranch2 Red key val
                  (Right . Left $ MkBranch1 leftKey leftVal child)
                  (case right of
                    Left (MkLeaf Red rightKey rightVal) => Left $ MkLeaf Black rightKey rightVal
                    Left (MkLeaf Black _ _) impossible
                  )
                )
              Nothing => Nothing
        Left left @(MkLeaf Black leftKey leftVal) =>
          let
            newLeft = insertLeaf {replace} newKey newVal left
          in if replace
            then case newLeft of
              Left (replaced, left) => Left (
                  replaced,
                  MkBranch2 Black key val (Left left) right
                )
              Right (MkBranch1 leftKey leftVal child) =>
                Right ((Black, key) ** MkBranch2 Black key val
                  (Right . Left $ MkBranch1 leftKey leftVal child)
                  right
                )
            else case newLeft of
              Just (MkBranch1 leftKey leftVal child) =>
                Just ((Black, key) ** MkBranch2 Black key val
                  (Right . Left $ MkBranch1 leftKey leftVal child)
                  right
                )
              Nothing => Nothing
        Right (Left left) => case left of
          MkBranch1 leftKey leftVal child =>
            let
              newLeft = insertBranch1 {replace} newKey newVal left
            in if replace
              then case newLeft of
                Left (replaced, left) => Left (
                    replaced,
                    MkBranch2 Black key val (Right $ Left left) right
                  )
                Right (leftKey ** left) => Right ((Black, key) **
                    MkBranch2 Black key val
                      {leftPrf = ?lp}
                      (Right . Right $ left)
                      right
                  )
              else ?r2
        Right (Right left) => ?r
      (No notEq ** Right gt) => ?n


-- mutual
--   data Tree
--     : (LinearOrder k rel, DecEq k) =>
--     k ->
--     ty ->
--     Type where
--     Leaf :
--       (LinearOrder k rel, DecEq k) =>
--       (col : Color) ->
--       (key : k) ->
--       (val : ty) ->
--       Tree {rel} key ty
--     Branch1 :
--       (LinearOrder k rel, DecEq k) =>
--       (key : k) ->
--       (val : ty) ->
--       {childKey : k} ->
--       (child : Tree {rel} childKey ty) ->
--       {auto 0 childRed : color child = Red} ->
--       Tree {rel} key ty
--     Branch2 :
--       (LinearOrder k rel, DecEq k) =>
--       (col : Color) ->
--       (key : k) ->
--       (val : ty) ->
--       (left : Tree {rel} leftKey ty) ->
--       (right : Tree {rel} rightKey ty) ->
--       {leftPrf : leftKey `rel` key} ->
--       {rightPrf : key `rel` rightKey} ->
--       {auto 0 heightEq : height left = height right} ->
--       {auto 0 notAdjacentReds : col = Red -> (color left = Black, color right = Black)} ->
--       Tree {rel} key ty

--   color : (LinearOrder k rel, DecEq k) => Tree {rel} key ty -> Color
--   color (Leaf col _ _) = col
--   color (Branch1 _ _ node) = Black
--   color (Branch2 col _ _ _ _) = col

--   height : (LinearOrder k rel, DecEq k) => Tree {rel} key ty -> Nat
--   height (Leaf Red _ _) = 0
--   height (Leaf Black _ _) = 1
--   height (Branch1 _ _ node) = S $ height node
--   height (Branch2 col _ _ left right) = case col of
--     Red => height left + height right
--     Black => S $ height left + height right

-- heightP : (LinearOrder k rel, DecEq k) => (node : Tree {rel} key ty) -> (child : Tree {rel} key' ty) -> {childRed : color child = Red} -> node = Branch1 {childRed} key val child -> height node = S (height child)

-- insert' :
--   (LinearOrder k rel, DecEq k) =>
--   (newKey : k) ->
--   (val : ty) ->
--   (tree : Tree {rel} key ty) ->
--   (tree' : Tree {rel} key ty ** Either (height tree' = height tree) (height tree' = S (height tree)))
-- insert' newKey newVal (Leaf Red key val) =
--   let
--     child = (Leaf Red newKey newVal ** ?h8)
--     res = Branch1 key val child {childRed = ?chr}
--   in (res ** Right (rewrite (heightP res child ?p) in ?h6))
-- insert' newKey newVal (Leaf Black key val) =
--   let res = Branch1 key val (Leaf Red newKey newVal) in (res ** ?h5)
-- insert' newKey newVal (Branch1 {childKey} key val child {childRed}) =
--   case key `decEq` newKey of
--     Yes eq => case newKey `decEq` childKey of
--       Yes eq' => rewrite eq in rewrite eq' in insert' newKey newVal child
--       No notEq => case connex {rel} notEq of
--         Left lt => case child of
--           Leaf col childKey childVal =>
--             Branch2 Black key val (Leaf Red newKey newVal) (Leaf Red childKey childVal) {notAdjacentReds = \x => absurd x}
--           Branch1 childKey childVal child impossible
--           Branch2 {heightEq} col childKey childVal left right =>
--             case (insert' newKey newVal left, right) of
--               Leaf col' key' val' => Branch2 Black key val (Leaf col' key' val') right {heightEq = ?he} {notAdjacentReds = \x => absurd x}
--               Branch1 key' val' child' => ?h1
--               Branch2 col' key' val' left' right' => ?h4
--               _ => ?rest
--             -- Branch2 Black key val (insert' newKey newVal left) right {heightEq = ?he} {notAdjacentReds = \x => absurd x}
--         Right _ => ?h3
--     No _ => ?h2
-- insert' newKey newVal (Branch2 col key val left right) = ?branch2
