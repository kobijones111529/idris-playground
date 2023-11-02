module Data.Set

import Data.List as L
import Data.So

data SortedList : {0 a : Type} -> {0 ord : Ord a} -> (xs : List a) -> {prf : sorted xs = True} -> Type where
  Nil : SortedList [] {prf = ?helpNil}
  One : Ord a => a -> SortedList [a] {prf = ?helpOne}

-- insert : SortedList xs -> SortedList xs
-- insert = ?he
