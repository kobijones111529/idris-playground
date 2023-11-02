module Data.IOArray3

import Control.Linear.LIO
import Data.Fin
import Data.IOArray.Prims

%default total

export
data Container : (size : Nat) -> (a : Type) -> Type where
  MkContainer : (size : Nat) -> ArrayData a -> Container size a

-- export
-- newArray3 : HasIO io => (size : Nat) -> (1 _ : (1 _ : Container size (Maybe a)) -> io ()) -> io ()
-- newArray3 size p =
--   let
--     (>>=) = bindL
--   in do
--     arrayData <- primIO $ prim__newArray (cast size) Nothing
--     p $ MkContainer size arrayData

export
newArray3 : (LinearBind io, HasLinearIO io) => (size : Nat) -> L1 io (Container size (Maybe a))
newArray3 size =
  do
    arrayData <- primIO $ prim__newArray (cast size) Nothing
    pure1 $ MkContainer size arrayData

export
readArray3 : (LinearBind io, HasLinearIO io) => (1 _ : Container size a) -> Fin size -> L1 io (Res a (const $ Container size a))
readArray3 (MkContainer size arrayData) pos = do
  el <- primIO $ prim__arrayGet arrayData (cast $ finToNat pos)
  pure1 $ el # MkContainer size arrayData

export
writeArray3 : (LinearBind io, HasLinearIO io) => (1 _ : Container size a) -> Fin size -> a -> L1 io (Container size a)
writeArray3 (MkContainer size arrayData) pos el = do
  primIO $ prim__arraySet arrayData (cast $ finToNat pos) el
  pure1 $ MkContainer size arrayData

export
deleteArray3 : (1 _ : Container _ _) -> ()
deleteArray3 (MkContainer _ _) = ()

export
swapArray3 : (LinearBind io, HasLinearIO io) => (1 _ : Container size a) -> Fin size -> Fin size -> L1 io (Container size a)
swapArray3 arr p p' = do
  el # arr <- readArray3 arr p
  el' # arr <- readArray3 arr p'
  arr <- writeArray3 arr p el'
  arr <- writeArray3 arr p' el
  pure1 arr
