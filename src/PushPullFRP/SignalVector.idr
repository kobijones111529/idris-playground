module PushPullFRP.SignalVector

import public PushPullFRP.SignalVector.Delta
import public PushPullFRP.SignalVector.EventInput
import public PushPullFRP.SignalVector.Handler
import public PushPullFRP.SignalVector.Occurrence
import public PushPullFRP.SignalVector.Sample
import public PushPullFRP.SignalVector.SignalUpdate
import public PushPullFRP.SignalVector.SignalVector

%default total

export
applyHandlerOccurrence : Handler out sv -> Occurrence sv -> out
applyHandlerOccurrence (HandlerEvent f) (MkOccurrence x) = f x
applyHandlerOccurrence (HandlerBoth handler _) (OccurrenceLeft occ) =
  applyHandlerOccurrence handler occ
applyHandlerOccurrence (HandlerBoth _ handler) (OccurrenceRight occ) =
  applyHandlerOccurrence handler occ

export
eventInputToOccurrence : EventInput sv -> Occurrence sv
eventInputToOccurrence (MkEventInput x) = MkOccurrence x
eventInputToOccurrence (EventInputLeft left) =
  OccurrenceLeft $ eventInputToOccurrence left
eventInputToOccurrence (EventInputRight right) =
  OccurrenceRight $ eventInputToOccurrence right

export
updateDelta : Delta sv -> SignalUpdate sv -> Delta sv
updateDelta _ (MkSignalUpdate x) = MkDelta x
updateDelta DeltaNothing (SignalUpdateLeft updateLeft) =
  DeltaBoth (updateDelta DeltaNothing updateLeft) DeltaNothing
updateDelta DeltaNothing (SignalUpdateRight updateRight) =
  DeltaBoth DeltaNothing (updateDelta DeltaNothing updateRight)
updateDelta (DeltaBoth deltaLeft deltaRight) (SignalUpdateLeft updateLeft) =
  DeltaBoth (updateDelta deltaLeft updateLeft) deltaRight
updateDelta (DeltaBoth deltaLeft deltaRight) (SignalUpdateRight updateRight) =
  DeltaBoth deltaLeft (updateDelta deltaRight updateRight)

export
applyHandlerDelta : Handler out sv -> Delta sv -> List out
applyHandlerDelta _ DeltaNothing = []
applyHandlerDelta (HandlerSignal f) (MkDelta x) = [f x]
applyHandlerDelta
  (HandlerBoth handlerLeft handlerRight)
  (DeltaBoth deltaLeft deltaRight) =
    let
      leftOut = applyHandlerDelta handlerLeft deltaLeft
      rightOut = applyHandlerDelta handlerRight deltaRight
    in leftOut ++ rightOut
