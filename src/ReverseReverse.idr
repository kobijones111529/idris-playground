module ReverseReverse

%hide Prelude.Types.List.reverse
%hide Prelude.Types.reverse
%hide Prelude.Types.SnocList.reverse

export
reverse : List a -> List a
reverse [] = []
reverse (x :: xs) = reverse xs ++ [x]

appendNil : (xs : List a) -> xs ++ [] = xs
appendNil [] = Refl
appendNil (x :: xs) =
  rewrite appendNil xs in Refl

appendCommutative : (xs : List a) -> (ys : List a) -> (zs : List a) -> (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
appendCommutative xs ys zs = ?appendCommutative_rhs

reverseAppend : (xs : List a) -> (ys : List a) -> reverse (xs ++ ys) = reverse ys ++ reverse xs
reverseAppend [] [] = Refl
reverseAppend [] (x :: xs) =
  rewrite appendNil (reverse xs ++ [x]) in Refl
reverseAppend (x :: xs) [] =
  rewrite reverseAppend xs [] in Refl
reverseAppend (x :: xs) (y :: ys) =
  rewrite reverseAppend xs (y :: ys) in
  rewrite appendCommutative (reverse ys ++ [y]) (reverse xs) [x] in Refl

export
reverseReverse : (xs : List a) -> reverse (reverse xs) = xs
reverseReverse [] = Refl
reverseReverse (x :: xs) =
  rewrite reverseAppend (reverse xs) [x] in
  rewrite reverseReverse xs in Refl
