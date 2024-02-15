module FizzBuzz

import Data.DPair
import Data.List
import Data.Nat

%default total

export
fizzBuzz : List (Subset Nat NonZero, String) -> Nat -> Maybe String
fizzBuzz xs x =
  case mapMaybe (uncurry ($>) . mapFst (guard . (== 0) . (\(Element n nz) => modNatNZ x n nz))) xs of
    [] => Nothing
    xs@(_ :: _) => Just $ foldl1 (++) xs
