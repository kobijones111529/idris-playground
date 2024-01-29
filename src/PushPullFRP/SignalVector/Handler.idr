module PushPullFRP.SignalVector.Handler

import PushPullFRP.SignalVector.SignalVector

%default total

public export
data Handler : out -> SignalVector -> Type where
  HandlerEmpty : Handler out Empty
  HandlerSignal : (a -> out) -> Handler out (Signal a)
  HandlerEvent : (a -> out) -> Handler out (Event a)
  HandlerBoth : Handler out left -> Handler out right -> Handler out (Append left right)

export
emptyHandler : Handler out Empty
emptyHandler = HandlerEmpty

export
signalHandler : (a -> out) -> Handler out (Signal a)
signalHandler = HandlerSignal

export
eventHandler : (a -> out) -> Handler out (Event a)
eventHandler = HandlerEvent

export
combineHandlers : Handler out left -> Handler out right -> Handler out (Append left right)
combineHandlers = HandlerBoth
