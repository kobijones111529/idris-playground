module Main

import Control.Monad.State
import Data.Fuel
import PushPullFRP
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
    init : EvalState IO (Empty) (Signal Double) := initEvalState
      (signalHandler printLn)
      (sampleNothing)
      0
      (time)
  loop {a = ()} forever init $ do
    t <- lift $ clockTime Monotonic
    let
      dt = t `timeDifference` t0
      secs = fromInteger (seconds dt) + fromInteger (nanoseconds dt) / 1000000000
    step secs
