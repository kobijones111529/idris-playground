module PushPullFRP.SignalVector.Sample

import PushPullFRP.SignalVector.SignalVector

%default total

public export
data Sample : SignalVector -> Type where
  MkSample : a -> Sample (Signal a)
  SampleEmpty : Sample Empty
  SampleEvent : Sample (Event a)
  SampleBoth : Sample left -> Sample right -> Sample (Append left right)

export
sample : a -> Sample (Signal a)
sample = MkSample

export
sampleNothing : Sample Empty
sampleNothing = SampleEmpty

export
sampleEvent : Sample (Event a)
sampleEvent = SampleEvent

export
combineSamples : Sample left -> Sample right -> Sample (Append left right)
combineSamples = SampleBoth

export
splitSamples : Sample (Append left right) -> (Sample left, Sample right)
splitSamples (SampleBoth left right) = (left, right)

export
sampleValue : Sample (Signal a) -> a
sampleValue (MkSample x) = x


