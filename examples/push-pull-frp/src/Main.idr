module Main

import Control.Monad.State
import Data.Fuel
import NCurses as NC
import PushPullFRP
import System
import System.Clock

%default total

loop : Monad m => Fuel -> EvalState m svIn svOut -> EvalT svIn svOut m a -> m a
loop Dry st eval = do
  (_, x) <- runEvalT st eval
  pure x
loop (More fuel) st eval = do
  (st', _) <- runEvalT st eval
  loop fuel st' eval

export
covering
main : IO ()
main = do
  t0 <- clockTime Monotonic
  let
    init : EvalState IO (Empty) (Event String) := initEvalState
      (eventHandler $ \str => NC.print str >> NC.print "\n")
      (sampleNothing)
      0
      (never)

  _ <- NC.init
  _ <- NC.cBreak
  _ <- NC.noEcho
  NC.print "Hello"
  _ <- NC.getChar

  loop {a = ()} forever init $ do
    t <- lift $ clockTime Monotonic
    let
      dt = t `timeDifference` t0
      secs = fromInteger (seconds dt) + fromInteger (nanoseconds dt) / 1000000000
    step secs

  NC.end

-- export
-- main : IO ()
-- main = do
--   _ <- NC.init
--   _ <- NC.cBreak
--   _ <- NC.noEcho
--   NC.print "Hello"
--   c <- NC.getChar
--   NC.print $ show c
--   _ <- NC.getChar
--   NC.end
--   pure ()
