module PushPullFRP.SignalVector.Delta

import PushPullFRP.SignalVector.SignalVector

%default total

public export
data Delta : SignalVector -> Type where
  MkDelta : a -> Delta (Signal a)
  DeltaNothing : Delta sv
  DeltaBoth : Delta left -> Delta right -> Delta (Append left right)

export
delta : a -> Delta (Signal a)
delta = MkDelta

export
deltaNothing : Delta sv
deltaNothing = DeltaNothing

export
combineDeltas : Delta left -> Delta right -> Delta (Append left right)
combineDeltas = DeltaBoth

export
splitDelta : Delta (Append left right) -> (Delta left, Delta right)
splitDelta DeltaNothing = (DeltaNothing, DeltaNothing)
splitDelta (DeltaBoth left right) = (left, right)

export
deltaValue : Delta (Signal a) -> Maybe a
deltaValue (MkDelta x) = Just x
deltaValue DeltaNothing = Nothing
