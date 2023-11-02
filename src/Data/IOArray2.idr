module Data.IOArray2

import Data.IOArray.Prims
import Data.Fin

%default total

export
record IOArray2 (0 len : Nat) elem where
  constructor MkIOArray2
  maxSize : Nat
  content : ArrayData (Maybe elem)

copyContent : forall elem. HasIO io => ArrayData elem -> ArrayData elem -> Nat -> io ()
copyContent src dst n = do
  el <- primIO $ prim__arrayGet src (cast n)
  primIO $ prim__arraySet dst (cast n) el
  case n of
    Z => pure ()
    S n' => copyContent src dst n'

export
newArray2 : forall elem. HasIO io => Nat -> io (IOArray2 0 elem)
newArray2 size = do
  content <- primIO $ prim__newArray (cast size) Nothing
  pure $ MkIOArray2 (cast size) content

export
writeArray2 : forall elem. HasIO io => IOArray2 len elem -> Fin len -> elem -> io (IOArray2 len elem)
writeArray2 arr pos el = do
  primIO $ prim__arraySet (content arr) (cast $ finToNat pos) (Just el)
  pure arr

export
readArray2 : forall elem. HasIO io => IOArray2 len elem -> Fin len -> io elem
readArray2 arr pos = do
  a <- primIO $ prim__arrayGet (content arr) (cast $ finToNat pos)
  pure $ assert_total $ case a of
    Just el => el

export
newArray2Copy : forall elem. HasIO io => {len : Nat} -> (newSize : Nat) -> IOArray2 len elem -> {_ : So (size >= len)} -> io (IOArray2 len elem)
newArray2Copy newSize arr = do
  newContent <- primIO $ prim__newArray (cast newSize) Nothing
  copyContent (content arr) newContent len
  pure $ MkIOArray2 newSize newContent

export
pushArray2 : forall elem. HasIO io => {len : Nat} -> IOArray2 len elem -> elem -> io (IOArray2 (S len) elem)
pushArray2 arr el =
  if len < maxSize arr
    then do
      primIO $ prim__arraySet (content arr) (cast len) (Just el)
      pure $ MkIOArray2 (S len) (content arr)
    else do
      newContent <- primIO $ prim__newArray (cast $ S (len * 2)) Nothing
      copyContent (content arr) newContent len
      primIO $ prim__arraySet newContent (cast len) (Just el)
      pure $ MkIOArray2 (S len) (newContent)
