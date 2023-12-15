module Data.String.AsVect

import public Data.String

strConsSuccLength : length (strCons c str) = S (length str)
strConsSuccLength = believe_me ()

public export
data AsVect : String -> Nat -> Type where
  Nil : AsVect "" Z
  (::) : (c : Char) -> Lazy (AsVect str (length str)) -> AsVect (strCons c str) (S $ length str)

public export
asVect : (str : String) -> AsVect str (length str)
asVect str with (strM str)
  asVect "" | StrNil = Nil
  asVect str@(strCons c str') | StrCons c str' =
    rewrite strConsSuccLength {c} {str = str'}
    in c :: asVect (assert_smaller str str')
