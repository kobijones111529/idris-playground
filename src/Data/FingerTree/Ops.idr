module Data.FingerTree.Ops

import public Data.FingerTree.Core
import Data.List
import Data.Nat
import Data.Vect

%default total

export
Nil : FingerTree ty
Nil = Empty

export
(::) : ty -> FingerTree ty -> FingerTree ty
(::) x Empty = Single x
(::) x (Single y) =
  let
    left = MkAffix [x]
    right = MkAffix [y]
  in Deep left Empty right
(::) x (Deep left deep right) =
  let MkAffix {n} {upper} xs = left
  in case n `isLT` 4 of
    Yes prf =>
      let left = MkAffix (x :: xs)
      in Deep left deep right
    No contra =>
      let
        prf = notLTImpliesGTE contra
        0 eq = antisymmetric upper prf
        y :: ys = xs
        left = MkAffix [x, y]
        0 eq = antisymmetric (fromLteSucc upper) (fromLteSucc prf)
        node = MkNode
          {lower = rewrite eq in %search}
          {upper = rewrite eq in %search}
          ys
        deep = node :: deep
      in Deep left deep right
      -- let
      --   prf = notLTImpliesGTE contra
      --   0 eq = antisymmetric prf upper
      -- in case xs of
      --   [a, b, c, d] =>
      --     let
      --       left = MkAffix [x, a]
      --       deep = (MkNode [b, c, d]) :: deep
      --     in Deep left deep right

export
Lin : FingerTree ty
Lin = Empty

export
(:<) : FingerTree ty -> ty -> FingerTree ty
(:<) Empty x = Single x
(:<) (Single x) y =
  let
    left = MkAffix [x]
    right = MkAffix [y]
  in Deep left Empty right
(:<) (Deep left deep right) x =
  let MkAffix {n = rightLen} {upper} xs = right
  in case isLT rightLen 4 of
    Yes prf =>
      let
        prf' = plusCommutative rightLen 1
        lower : LTE 1 (rightLen + 1) := rewrite prf' in %search
        upper : LTE (rightLen + 1) 4 := rewrite prf' in prf
        right = MkAffix (xs ++ [x])
      in Deep left deep right
    No contra =>
      let
        prf = notLTImpliesGTE contra
        0 eq = antisymmetric prf upper
      in case xs of
        [a, b, c, d] =>
          let
            deep = deep :< MkNode [a, b, c]
            right = MkAffix [d, x]
          in Deep left deep right

public export
head : (xs : FingerTree ty) -> {auto 0 _ : NonEmpty xs} -> ty
head (Single x) = x
head (Deep left _ _) =
  let MkAffix {n = S _} start = left
  in head start

public export
last : (xs : FingerTree ty) -> {auto 0 _ : NonEmpty xs} -> ty
last (Single x) = x
last (Deep _ _ right) =
  let MkAffix {n = S _} end = right
  in last end

public export
uncons : (xs : FingerTree ty) -> {auto 0 _ : NonEmpty xs} -> (ty, FingerTree ty)
uncons (Single x) = (x, Empty)
uncons (Deep left deep right) =
  let
    MkAffix {n = S n} {upper} (x :: xs) = left
  in case n `isGTE` 1 of
    Yes prf =>
      let
        0 upper = lteSuccLeft upper
        left = MkAffix xs
      in (x, Deep left deep right)
    No contra =>
      let (LTEZero) = notLTImpliesGTE contra
      in case deep of
        Empty =>
          let MkAffix {n = S m} {upper = upper'} (y :: ys) = right
          in case m `isGTE` 1 of
            Yes prf =>
              let
                0 upper' = lteSuccLeft upper'
                left = MkAffix $ xs ++ [y]
                right = MkAffix ys
              in (x, Deep left Empty right)
            No contra => (x, Single y)
        Single node =>
          let
            MkNode {lower = LTESucc lower'} {upper = upper'} ys = node
            0 lower' = lteSuccRight lower'
            0 upper' = lteSuccRight upper'
            left = MkAffix ys
          in (x, Deep left Empty right)
        deep@(Deep _ _ _) =>
          let
            (node, deep) = uncons deep
            MkNode {lower = LTESucc lower'} {upper = upper'} ys = node
            0 lower' = lteSuccRight lower'
            0 upper' = lteSuccRight upper'
            left = MkAffix ys
          in (x, Deep left deep right)

-- unconsConsSame : (tree : FingerTree ty) -> {0 nonEmpty : NonEmpty tree} -> uncurry (::) (uncons tree) = tree
-- unconsConsSame (Single _) = Refl
-- unconsConsSame (Deep left deep right) =
--   let
--     MkAffix {n = S n} {upper} (x :: xs) = left
--   in case n `isGTE` 1 of
--     Yes prf =>
--       let
--         0 upper = lteSuccLeft upper
--         left = MkAffix xs
--       in ?h1
--     No contra =>
--       let (LTEZero) = notLTImpliesGTE contra
--       in case deep of
--         Empty =>
--           let MkAffix {n = S m} {upper = upper'} (y :: ys) = right
--           in case m `isGTE` 1 of
--             Yes prf =>
--               let
--                 0 upper' = lteSuccLeft upper'
--                 left = MkAffix $ xs ++ [y]
--                 right = MkAffix ys
--               in ?h2
--             No contra => ?h3
--         Single node =>
--           let
--             MkNode {lower = LTESucc lower'} {upper = upper'} ys = node
--             0 lower' = lteSuccRight lower'
--             0 upper' = lteSuccRight upper'
--             left = MkAffix ys
--           in ?h4
--         deep@(Deep _ _ _) =>
--           let
--             (node, deep) = uncons deep
--             MkNode {lower = LTESucc lower'} {upper = upper'} ys = node
--             0 lower' = lteSuccRight lower'
--             0 upper' = lteSuccRight upper'
--             left = MkAffix ys
--           in ?h5

namespace List
  public export
  data View : FingerTree ty -> Type where
    Nil : View Empty
    (::) : (x : ty) -> (xs : FingerTree ty) -> View (x :: xs)

  -- view : (tree : FingerTree ty) -> View tree
  -- view Empty = Nil
  -- view tree@(Single _) =
  --   let
  --     (x, xs) = uncons tree
  --   in ?h
  -- view (Deep x y z) = ?h_2

-- namespace List
--   public export
--   data View : FingerTree ty -> Type where
--     Nil : View Empty
--     (::) : (x : ty) -> (xs : FingerTree ty) -> View (x :: xs)

--   export
--   view : (xs : FingerTree ty) -> View xs
--   view Empty = []
--   view (Single x) = [x]
--   view (Deep left deep right) = ?h_2
