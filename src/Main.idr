module Main

import Data.List
import Data.List.Elem
import Data.Nat.LT
import Data.RedBlackTree
import Decidable.Equality
import System
import System.Clock

main : IO ()
main = do
  let
    size = 1000
  listBench (S size) size
  treeBench (S size) size
  where
    listBench : Nat -> Nat -> IO ()
    listBench size search = do
      startTime <- clockTime Monotonic
      let list : List Nat := foldr (\el, acc => case isElem el acc of { Yes _ => acc ; No _ => el :: acc }) [] [1..size]
      endTime <- clockTime Monotonic
      putStrLn $ "Construction time: " ++ show (timeDifference endTime startTime)
      startTime <- clockTime Monotonic
      printLn $ find (== search) list
      endTime <- clockTime Monotonic
      putStrLn $ "Lookup time: " ++ show (timeDifference endTime startTime)

    treeBench : Nat -> Nat -> IO ()
    treeBench size search = do
      startTime <- clockTime Monotonic
      let
        tree : BinarySearchTree Nat LT := foldr (\el, acc => insert el acc) (empty {rel = LT}) (reverse [1..size])
      endTime <- clockTime Monotonic
      putStrLn $ "Construction time: " ++ show (timeDifference endTime startTime)
      printLn . length . show @{ShowBST} $ tree
      startTime <- clockTime Monotonic
      -- printLn $ lookup search tree
      endTime <- clockTime Monotonic
      putStrLn $ "Lookup time: " ++ show (timeDifference endTime startTime)


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
