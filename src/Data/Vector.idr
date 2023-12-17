module Data.Vector

import Control.Linear.LIO
import Data.Nat
import Data.Vect
import Data.IOArray.Prims

%default total

namespace Sized
  export
  record SizedArrayData (n : Nat) a where
    constructor MkSizedArrayData
    internal : ArrayData a

  export
  newArray : (n : Nat) -> a -> IO (SizedArrayData n a)
  newArray n x = do
    arrayData <- primIO $ prim__newArray (cast n) x
    pure $ MkSizedArrayData arrayData

  export
  writeArray : SizedArrayData n a -> Fin n -> a -> IO ()
  writeArray arrayData i x =
    primIO $ prim__arraySet (internal arrayData) (cast . finToNat $ i) x

  export
  readArray : SizedArrayData n a -> Fin n -> IO a
  readArray arrayData i =
    primIO $ prim__arrayGet (internal arrayData) (cast . finToNat $ i)

record Array (n : Nat) a where
  constructor MkArray
  internal : SizedArrayData n (Maybe a)

-- replicate : (n : Nat) -> a -> Array n a
-- replicate n x = MkArray $ unsafePerformIO $ newArray n (Just x)

replicate : (n : Nat) -> a -> L1 io (Array n a)
replicate n x = pure1 $ MkArray $ unsafePerformIO $ newArray n (Just x)

index : Fin n -> (1 _ : Array n a) -> L1 io (Res a (const $ Array n a))
index i (MkArray internal) = 
  let
    -- Silently perform IO read
    x = unsafePerformIO $ readArray internal i
    -- Assert value exists at index
    _ = the (IsJust x) $ believe_me x
  in pure1 (fromJust x # MkArray internal)

replaceAt : Fin n -> a -> (1 _ : Array n a) -> L1 io (Array n a)
replaceAt i x (MkArray internal) =
  let
    -- Silently perform IO write
    _ = unsafePerformIO $ writeArray internal i $ Just x
  in pure1 $ MkArray internal

updateAt : LinearBind io => Fin n -> (a -> a) -> (1 _ : Array n a) -> L1 io (Array n a)

fromVect : {n : Nat} -> Vect n a -> Array n a
fromVect {n} xs = MkArray $ unsafePerformIO $ do
    d <- newArray n Nothing
    sequence_ $ (uncurry $ \x, i => writeArray d i (Just x)) <$> zip xs (allFins n)
    pure d
