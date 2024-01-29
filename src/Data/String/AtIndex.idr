module Data.String.AtIndex

import Data.DPair
import Data.String
import Data.String.Extra
import Data.String.Extra1
import Data.String.Sugar
import Decidable.Equality

%hide Prelude.List.length
%hide Prelude.SnocList.length

%default total

public export
data HasLength : Nat -> String -> Type where
  DoesHaveLength : HasLength (length str) str

export
hasLength : (0 str : String) -> HasLength (length str) str
hasLength _ = DoesHaveLength

export
hasLengthUnique : HasLength m xs -> HasLength n xs -> m === n
hasLengthUnique DoesHaveLength DoesHaveLength = Refl

export
appendPlusLengths : (0 xs : String) -> (0 ys : String) -> length (xs ++ ys) = length xs + length ys
appendPlusLengths xs ys = believe_me $ the (length (xs ++ ys) = _) Refl

export
hasLengthAppend : HasLength m xs -> HasLength n ys -> HasLength (m + n) (xs ++ ys)
hasLengthAppend DoesHaveLength DoesHaveLength = rewrite sym $ appendPlusLengths xs ys in DoesHaveLength

export
reverseSameLength : (0 xs : String) -> length (reverse xs) = length xs
reverseSameLength xs = believe_me $ the (length (reverse xs) = _) Refl

export
hasLengthReverse : HasLength n xs -> HasLength n (reverse xs)
hasLengthReverse DoesHaveLength = rewrite sym $ reverseSameLength xs in DoesHaveLength

public export
data AtIndex : Char -> String -> Nat -> Type where
  IsAtIndex : {xs, ys : String} -> AtIndex c (xs ++ c :: ys) (length xs)

splitAround : AtIndex c str n -> (String, String)
splitAround (IsAtIndex {xs} {ys}) = (xs, ys)
