module PushPullFRP.SignalVector.Occurrence

import PushPullFRP.SignalVector.SignalVector

%default total

public export
data Occurrence : SignalVector -> Type where
  MkOccurrence : a -> Occurrence (Event a)
  OccurrenceLeft : Occurrence left -> Occurrence (Append left right)
  OccurrenceRight : Occurrence right -> Occurrence (Append left right)

export
occurrence : a -> Occurrence (Event a)
occurrence = MkOccurrence

export
occurrenceLeft : Occurrence left -> Occurrence (Append left right)
occurrenceLeft = OccurrenceLeft

export 
occurrenceRight : Occurrence right -> Occurrence (Append left right)
occurrenceRight = OccurrenceRight

export
fromOccurrence : Occurrence (Event a) -> a
fromOccurrence (MkOccurrence x) = x

export
chooseOccurrence : Occurrence (Append left right) -> Either (Occurrence left) (Occurrence right)
chooseOccurrence (OccurrenceLeft left) = Left left
chooseOccurrence (OccurrenceRight right) = Right right
