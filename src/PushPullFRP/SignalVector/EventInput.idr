module PushPullFRP.SignalVector.EventInput

import PushPullFRP.SignalVector.Routable
import PushPullFRP.SignalVector.SignalVector

%default total

public export
data EventInput : SignalVector -> Type where
  MkEventInput : a -> EventInput (Event a)
  EventInputLeft : EventInput left -> EventInput (Append left right)
  EventInputRight : EventInput right -> EventInput (Append left right)

export
event : a -> EventInput (Event a)
event = MkEventInput

export
Routable EventInput where
  routeLeft = EventInputLeft
  routeRight = EventInputRight


