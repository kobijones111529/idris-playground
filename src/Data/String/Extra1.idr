module Data.String.Extra1

import Control.Relation
import Data.DPair
import Data.List
import Data.List1
import Data.Singleton
import Data.SnocList
import Data.String
import Data.String.AsSnocList
import Data.String.Extra
import Data.String.Sugar
import Decidable.Equality

%hide Data.List.span
%hide Data.String.span

%default total

strUnsnoc : String -> Maybe (String, Char)
strUnsnoc "" = Nothing
strUnsnoc str =
  let
    len = strLength str
  in assert_total $ Just (strSubstr 0 (len - 1) str, strIndex str len)

public export
replicate : Nat -> Char -> String
replicate n c = rec n c []
  where
    rec : Nat -> Char -> String -> String
    rec Z _ acc = acc
    rec (S n) c acc = rec n c (c :: acc)

public export
span : (Char -> Bool) -> String -> (String, Maybe String)
span p str = span' p str $ asList str
  where
    span' : (Char -> Bool) -> (0 str : String) -> AsList str -> (String, Maybe String)
    span' p [] [] = ([], Nothing)
    span' p (c :: str) (c :: xs) =
      if p c
        then mapFst (c ::) $ span' p str xs
        else ([], Just str)

spanTR : String -> (Char -> Bool) -> String -> (String, Maybe String)
spanTR acc p str = rec acc p str $ asList str
  where
    rec : String -> (Char -> Bool) -> (0 str : String) -> AsList str -> (String, Maybe String)
    rec acc p [] [] = (acc, Nothing)
    rec acc p (c :: str) (c :: xs) =
      if p c
        then rec (acc :< c) p str xs
        else (acc, Just $ c :: str)

%transform "tailRecSpan" span = spanTR ""

public export
split : (Char -> Bool) -> String -> List1 String
split p str = split' p str $ asList str
  where
    split' : (Char -> Bool) -> (0 str : String) -> AsList str -> List1 String
    split' p [] [] = [] ::: []
    split' p (c :: str) (c :: xs) =
      if p c
        then [] ::: forget (split' p str xs)
        else case split' p str xs of
          str ::: xs => (c :: str) ::: xs

splitTR : (Char -> Bool) -> String -> List1 String
splitTR p str = rec [<] [] p $ asList str
  where
    rec : {0 str : String} -> SnocList String -> String -> (Char -> Bool) -> AsList str -> List1 String
    rec strs str _ [] with (toList strs)
      _ | [] = singleton str
      _ | x :: xs = x ::: xs ++ [str]
    rec strs str p (c :: cs) =
      if p c
        then rec (strs :< str) [] p cs
        else rec strs (str :< c) p cs

export
appendNilRightNeutral : (str : String) -> str ++ "" = str

export
appendNilLeftNeutral : (str : String) -> "" ++ str = str

data Prefix : String -> String -> Type where
  IsPrefix : (pre : String) -> (suff : String) -> Prefix pre (pre ++ suff)

consIsAppend : strCons c str = singleton c ++ str

appendConsIsSnocAppend : (x : String) -> (c : Char) -> (y : String) -> x ++ strCons c y = strSnoc x c ++ y

isPrefixOfHelp : (acc : String) -> (0 pre, str : String) -> AsList pre -> AsList str -> Maybe (Prefix (acc ++ pre) (acc ++ str))
isPrefixOfHelp acc "" "" [] [] = Just $ lemma $ IsPrefix acc ""
  where
    lemma : Prefix acc (acc ++ str) -> Prefix (acc ++ "") (acc ++ str)
    lemma pre = rewrite appendNilRightNeutral acc in pre
isPrefixOfHelp acc "" (strCons c str) [] (_ :: _) = Just $
  rewrite appendNilRightNeutral acc in
    IsPrefix acc (strCons c str)
isPrefixOfHelp acc (strCons c str) "" (c :: x) [] = Nothing
isPrefixOfHelp acc (strCons c str) (strCons d str') (c :: x) (d :: y) =
  case decEq c d of
    Yes yes =>
      rewrite yes in
      rewrite appendConsIsSnocAppend acc d str in
      rewrite appendConsIsSnocAppend acc d str' in
        isPrefixOfHelp (strSnoc acc d) str str' x y
    No no => Nothing

isPrefixOf : (pre : String) -> (str : String) -> Maybe (Prefix pre str)
isPrefixOf pre str =
  rewrite sym $ appendNilLeftNeutral str in
  rewrite sym $ appendNilLeftNeutral pre in
    isPrefixOfHelp [] pre str (asList pre) (asList str)

matchPrefix : (0 sep, str : String) -> AsList sep -> AsList str -> Maybe (str ** AsList str)
matchPrefix [] [] [] [] = Just ([] ** [])
matchPrefix [] (c :: str) [] (c :: xs) = Just (c :: str ** c :: xs)
matchPrefix (_ :: _) [] (_ :: _) [] = Nothing
matchPrefix (c :: sep) (c' :: str) (c :: xs) (c' :: ys) =
  if c == c'
    then case matchPrefix sep str xs ys of
      Just (str' ** xs') => Just (c :: str' ** c :: xs')
      Nothing => Nothing
    else Nothing

public export
splitByHelp : String -> (0 str : String) -> AsList str -> List1 String
splitByHelp sep [] [] = [] ::: []
splitByHelp sep (c :: str) (c :: xs) =
  case matchPrefix sep (c :: str) (asList sep) (c :: xs) of
    Just (rest ** ys) => [] ::: forget (splitByHelp sep rest $ assert_smaller (c :: xs) ys)
    Nothing => case splitByHelp sep str xs of
      y ::: ys => (c :: y) ::: ys

public export
splitBy : (sep : String) -> String -> List1 String
splitBy sep str = splitByHelp sep str (asList str)

0 spanTRIsSpan : spanTR "" p str = span p str
-- spanTRIsSpan = ?rhs
--   where
--     lemma : (acc : String) -> (p : Char -> Bool) -> (str : String) -> spanTR acc p str = mapFst (acc ++) (span p str)
--     lemma acc p str with (asList str)
--       lemma acc p "" | Nil = ?h1
--       lemma acc p (strCons c _) | (::) c xs = ?h2



data Suffix : String -> String -> Type where
  Same : Suffix xs xs
  Uncons : Suffix (x :: xs) ys -> Suffix xs ys

test1 : Suffix "c" "abc"
test1 = Uncons {x = 'b'} $ Uncons {x = 'a'} Same

appendLeftConsIsConsAppend : (x : Char) -> (xs : String) -> (ys : String) -> (x :: xs) ++ ys = x :: xs ++ ys
-- appendLeftConsIsConsAppend x xs ys = ?h2

suffixAppend : (xs, ys : String) -> Suffix ys (xs ++ ys)
suffixAppend xs ys = help xs ys (asSnocList xs) (asSnocList ys)
  where
    help : (xs, ys : String) -> AsSnocList xs -> AsSnocList ys -> Suffix ys (xs ++ ys)
    -- help [<] ysStr [<] ys = rewrite appendNilLeftNeutral ysStr in Same
    -- help xsStr [<] xs [<] = ?h3
    -- help (xsStr :< x) (ysStr :< y) (xs :< x) (ys :< y) =
    --   case decEq y x of
    --     Yes prf => rewrite prf in ?h1--help xsStr ysStr xs ys
    --     No contra => ?h2
