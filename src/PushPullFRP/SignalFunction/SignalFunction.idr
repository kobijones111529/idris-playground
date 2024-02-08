module PushPullFRP.SignalFunction.SignalFunction

import PushPullFRP.SignalVector

%default total

public export
data InitState = Initialized | Uninitialized

public export
data SF : InitState -> SignalVector -> SignalVector -> Type where
  MkSF : (Sample svIn -> (Sample svOut, SF Initialized svIn svOut)) -> SF Uninitialized svIn svOut
  SFInit :
    (Double -> Delta svIn -> (Delta svOut, List (Occurrence svOut), Inf (SF Initialized svIn svOut))) ->
    (Occurrence svIn -> (List (Occurrence svOut), Inf (SF Initialized svIn svOut))) ->
    SF Initialized svIn svOut

public export
(:~>) : SignalVector -> SignalVector -> Type
(:~>) left right = SF Uninitialized left right

infixl 10 :~>

export
apply : SF Initialized svIn svOut -> List (Occurrence svIn) -> (List (Occurrence svOut), SF Initialized svIn svOut)
apply sf =
  foldr
    (\evtOcc, (changes, SFInit _ changeCont) =>
      let (newChanges, newSF) = changeCont evtOcc
      in (newChanges ++ changes, newSF)
    )
    ([], sf)

composeInit : SF Initialized svIn svMiddle -> SF Initialized svMiddle svOut -> SF Initialized svIn svOut
composeInit (SFInit dtCont1 inputCont1) sf2@(SFInit dtCont2 _) =
  SFInit
    (\dt, delta =>
      let
        (sf1MemOutput, sf1EvtOutputs, sf1New) = dtCont1 dt delta
        (sf2MemOutput, sf2EvtOutputs, sf2New) = dtCont2 dt sf1MemOutput
        (sf2EvtEvtOutputs, sf2Newest) = apply sf2New sf1EvtOutputs
      in (sf2MemOutput, sf2EvtOutputs ++ sf2EvtEvtOutputs, composeInit sf1New sf2Newest)
    )
    (\evtOcc =>
      let
        (sf1Outputs, newSF1) = inputCont1 evtOcc
        (sf2FoldOutputs, newSF2) = apply sf2 sf1Outputs
      in (sf2FoldOutputs, composeInit newSF1 newSF2)
    )

export
compose : svIn :~> svMiddle -> svMiddle :~> svOut -> svIn :~> svOut
compose (MkSF sampleF1) (MkSF sampleF2) =
  MkSF $ \sample =>
    let
      (sample', sfInit1) = sampleF1 sample
      (sample'', sfInit2) = sampleF2 sample'
    in (sample'', composeInit sfInit1 sfInit2)

ignoreInit : SF Initialized sv Empty
ignoreInit =
  SFInit
    (\_, _ => (deltaNothing, [], ignoreInit))
    (\_ => ([], ignoreInit))

export
ignore : sv :~> Empty
ignore = MkSF $ \_ => (sampleNothing, ignoreInit)

constantInit : SF Initialized Empty (Signal a)
constantInit =
  SFInit
    (\_, _ => (deltaNothing, [], constantInit))
    (\_ => ([], constantInit))

export
constant : a -> Empty :~> Signal a
constant x = MkSF $ \_ => (sample x, constantInit)

identityInit : SF Initialized sv sv
identityInit = SFInit (\_, delta => (delta, [], identityInit)) (\evtOcc => ([evtOcc], identityInit))

export
identity : sv :~> sv
identity = MkSF (, identityInit)

timeInit : Double -> SF Initialized Empty (Signal Double)
timeInit t =
  SFInit
    (\dt, _ => (delta $ t + dt, [], timeInit $ t + dt))
    (\_ => ([], timeInit t))

export
time : Empty :~> Signal Double
time = MkSF $ \_ => (sample 0, timeInit 0)

neverInit : SF Initialized Empty (Event a)
neverInit =
  SFInit
    (\_, _ => (deltaNothing, [], neverInit))
    (\_ => ([], neverInit))

export
never : Empty :~> Event a
never = MkSF $ \_ => (sampleEvent, neverInit)
