module Main

import Data.Fuel
import Data.Stream
import Data.String.Extra1
import Test.Lexer as Lexer
import Test.Http as Http

%default total

runStream : Fuel -> a -> Stream (a -> IO (Either b a)) -> IO (Either a b)
runStream Dry acc (x :: _) =
  pure $ case !(x acc) of
    Left quitVal => Right quitVal
    Right val => Left val
runStream (More fuel) acc (x :: xs) =
  case !(x acc) of
    Left quitVal => pure $ Right quitVal
    Right val => runStream fuel val xs

covering
main : IO ()
main = Http.main

-- covering
-- main : IO ()
-- main = do
--   ignore $ runStream forever () $ repeat $ const $ (\quit => if quit then Left () else Right ()) <$> Lexer.main

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
