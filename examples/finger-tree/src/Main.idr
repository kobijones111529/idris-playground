module Main

import Data.FingerTree.Ops

%default total

export
main : IO ()
main =
  let
    a : FingerTree Nat := [< 1, 2, 3, 4, 5, 6, 7, 8, 9]
    a = 20 :: 21 :: 22 :: 23 :: 24 :: 25 :: a
  in printLn a
