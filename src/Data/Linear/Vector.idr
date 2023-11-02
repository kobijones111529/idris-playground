module Data.Linear.Vector

import Data.Fin
import Data.IOArray

public export
interface Vector vect where
	read : (1 _ : vect len t) -> Fin len -> Maybe t

public export
interface Vector vect => MVector vect where
	newVector : (1 _ : (1 _ : vect 0 t) -> a) -> a
	write : {len : Nat} -> (1 _ : vect len t) -> Fin len -> t -> Res Bool (const $ vect len t)

export
data LinVector : Nat -> Type -> Type where
	MkLinVector : IOArray t -> LinVector len t

export
Vector LinVector where
	read (MkLinVector a) i = unsafePerformIO $ readArray a (cast $ finToNat i)

export
MVector LinVector where
	newVector k = k (MkLinVector $ unsafePerformIO $ newArray 0)
	write (MkLinVector vect) i a = unsafePerformIO $
		do
			ok <- writeArray vect (cast $ finToNat i) a
			pure $ ok # MkLinVector vect

resize : (1 _ : LinVector len t) -> (newLen : Nat) -> LinVector newLen t
resize (MkLinVector vect) newLen = MkLinVector $ unsafePerformIO $ newArrayCopy (cast newLen) vect
