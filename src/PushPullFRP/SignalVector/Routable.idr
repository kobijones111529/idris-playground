module PushPullFRP.SignalVector.Routable

import PushPullFRP.SignalVector.SignalVector

%default total

public export
interface Routable (r : SignalVector -> Type) where
  routeLeft : r left -> r (Append left right)
  routeRight : r right -> r (Append left right)
