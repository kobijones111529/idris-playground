module PushPullFRP.SignalVector.SignalUpdate

import PushPullFRP.SignalVector.Routable
import PushPullFRP.SignalVector.SignalVector

%default total

public export
data SignalUpdate : SignalVector -> Type where
  MkSignalUpdate : a -> SignalUpdate (Signal a)
  SignalUpdateLeft : SignalUpdate left -> SignalUpdate (Append left right)
  SignalUpdateRight : SignalUpdate right -> SignalUpdate (Append left right)

export
Routable SignalUpdate where
  routeLeft = SignalUpdateLeft
  routeRight = SignalUpdateRight

export
updateSignal : a -> SignalUpdate (Signal a)
updateSignal = MkSignalUpdate
