module Data.String.Sugar

import public Data.String.Extra

%default total

public export
Nil : String
Nil = ""

public export
(::) : Char -> String -> String
(::) = strCons

public export
Lin : String
Lin = ""

public export
(:<) : String -> Char -> String
(:<) = strSnoc
