module PushPullFRP.SignalVector.SignalVector

%default total

public export
data SignalVector : Type where
  Empty : SignalVector
  Signal : Type -> SignalVector
  Event : Type -> SignalVector
  Append : SignalVector -> SignalVector -> SignalVector
