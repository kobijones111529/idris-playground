module Data.String.AsSnocList

import Data.String
import Data.String.Sugar

%default total

public export
data SnocStrM : String -> Type where
  StrLin : SnocStrM ""
  StrSnoc : (str : String) -> (c : Char) -> SnocStrM (str :< c)

public export
snocStrM : (str : String) -> SnocStrM str
snocStrM "" = StrLin
snocStrM str = assert_total $
  let
    len = strLength str
    init = strSubstr 0 (len - 1) str
    last = strIndex str len
  in believe_me $ StrSnoc init last

public export
data AsSnocList : String -> Type where
  Lin : AsSnocList []
  (:<) : {str : String} -> Lazy (AsSnocList str) -> (c : Char) -> AsSnocList (str :< c)

public export
asSnocList : (str : String) -> AsSnocList str
asSnocList str with (snocStrM str)
  asSnocList [] | StrLin = [<]
  asSnocList str@(xs :< x) | StrSnoc _ _ = asSnocList (assert_smaller str xs) :< x
