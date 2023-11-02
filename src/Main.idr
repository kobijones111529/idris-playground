module Main

-- import Data.BinarySearchTree
import Data.Nat.LT
import Data.RedBlackTree
import Decidable.Equality

main : IO ()
main = do
  let
    a : BinarySearchTree Nat LT
    a = empty {rel = LT}
    b = insert 1 a
    c = insert 8 . insert 7 . insert 6 . insert 5 . insert 4 . insert 3 . insert 2 $ b
  putStrLn . show @{ShowBST} $ c

-- main : IO ()
-- main = do
-- 	_ <- run $ do
-- 		arr <- newArray3 1 {a=Nat}
-- 		arr <- writeArray3 arr 0 (Just 2)
-- 		a # arr' <- readArray3 arr 0
-- 		printLn a
-- 		pure1 $ deleteArray3 arr'
-- 		pure ()
-- 	pure ()
-- 	let a : (t : Type ** t) := (Nat ** 1)
-- 	case a of
-- 		(Nat ** n) => printLn n
-- 		_ => printLn "bye"
