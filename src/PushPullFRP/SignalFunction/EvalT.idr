module PushPullFRP.SignalFunction.EvalT

import Control.Monad.State
import PushPullFRP.SignalVector
import PushPullFRP.SignalFunction.SignalFunction

%default total

public export
record EvalState (m : Type -> Type) svIn svOut where
  constructor MkEvalState
  sf : SF Initialized svIn svOut
  outputHandlers : Handler (m ()) svOut
  lastTime : Double
  delta : Delta svIn

public export
data EvalT : SignalVector -> SignalVector -> (Type -> Type) -> Type -> Type where
  MkEvalT : StateT (EvalState m svIn svOut) m a -> EvalT svIn svOut m a

public export
Functor m => Functor (EvalT svIn svOut m) where
  map f (MkEvalT st) = MkEvalT $ map f st

public export
Monad m => Applicative (EvalT svIn svOut m) where
  pure = MkEvalT . pure
  MkEvalT f <*> MkEvalT st = MkEvalT $ f <*> st

public export
Monad m => Monad (EvalT svIn svOut m) where
  MkEvalT st >>= f = MkEvalT $ do
    x <- st
    let MkEvalT st' = f x
    st'

public export
MonadTrans (EvalT svIn svOut) where
  lift = MkEvalT . lift

public export
(Monad m, Alternative m) => Alternative (EvalT svIn svOut m) where
  empty = MkEvalT empty
  MkEvalT x <|> MkEvalT y = MkEvalT $ x <|> y

public export
HasIO m => HasIO (EvalT svIn svOut m) where
  liftIO = MkEvalT . liftIO

export
initEvalState : Handler (m ()) svOut -> Sample svIn -> Double -> SF Uninitialized svIn svOut -> EvalState m svIn svOut
initEvalState handlers initSample initTime (MkSF sampleF) =
  let
    (_, sf) = sampleF initSample
  in MkEvalState
    { sf
    , outputHandlers = handlers
    , lastTime = initTime
    , delta = deltaNothing
    }

export
runEvalT' : EvalT svIn svOut m a -> EvalState m svIn svOut -> m (EvalState m svIn svOut, a)
runEvalT' (MkEvalT st) = runStateT' st

export
runEvalT : EvalState m svIn svOut -> EvalT svIn svOut m a -> m (EvalState m svIn svOut, a)
runEvalT = flip runEvalT'

export
push : Monad m => EventInput svIn -> EvalT svIn svOut m ()
push evtIn = MkEvalT $ do
  evalState <- get
  let
    evtOcc = eventInputToOccurrence evtIn
    (SFInit _ occCont) = evalState.sf
    (occs, newSF) = occCont evtOcc
  lift $ traverse_ (applyHandlerOccurrence evalState.outputHandlers) occs
  put $ { sf := newSF } evalState

export
update : Monad m => SignalUpdate svIn -> EvalT svIn svOut m ()
update sigUpdate = MkEvalT $ modify { delta $= flip updateDelta sigUpdate }

export
step : Monad m => Double -> EvalT svIn svOut m ()
step t = MkEvalT $ do
  evalState <- get
  let
    dt = t - evalState.lastTime
    (SFInit sampleF _) = evalState.sf
    (deltaOut, occsOut, newSF) = sampleF dt evalState.delta
  _ <- lift $ sequence $ applyHandlerDelta evalState.outputHandlers deltaOut
  lift $ traverse_ (applyHandlerOccurrence evalState.outputHandlers) occsOut
  put $ { lastTime := t, delta := deltaNothing, sf := newSF } evalState