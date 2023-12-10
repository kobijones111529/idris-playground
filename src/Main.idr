module Main

import Test.Lexer as Lexer

main : IO ()
main = Lexer.main

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
