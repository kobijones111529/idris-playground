module IOVect

import Data.Fin
import Data.Vect
import Data.IOArray.Prims

%default total

%hide Prelude.Types.elem

export
record IOVect Nat elem where
	constructor MkIOVect
	content : ArrayData (Maybe elem)

export
newVect : HasIO io => {len : Nat} -> io (IOVect len elem)
newVect {len} = do
	array <- primIO $ prim__newArray (cast len) Nothing
	pure (MkIOVect array)

export
writeVect : HasIO io => IOVect len elem -> Fin len -> elem -> io ()
writeVect vect pos el = primIO $ prim__arraySet (content vect) (cast . finToNat $ pos) (Just el)

export
readVect : HasIO io => IOVect len elem -> Fin len -> io elem
readVect vect pos = do
	res <- primIO $ prim__arrayGet (content vect) (cast . finToNat $ pos)
	case res of
		Just elem => pure elem
		Nothing => ?a

export
newVectCopy : HasIO io => {len : Nat} -> (newLen : Nat) -> (source : IOVect len elem) -> io (IOVect newLen elem)
newVectCopy {len} newLen source = do
	vect <- newVect
	case len of
		S k => copyFrom (content source) (content vect) k
		Z => pure ()
	pure vect
	where
		copyFrom : (src : ArrayData (Maybe elem)) -> (dest : ArrayData (Maybe elem)) -> (len : Nat) -> io ()
		copyFrom _ _ Z = pure ()
		copyFrom src dest pos @ (S prev) = do
			el <- primIO $ prim__arrayGet src (cast pos)
			primIO $ prim__arraySet dest (cast pos) el
			copyFrom src dest prev

fromVect : HasIO io => {len : Nat} -> Vect len elem -> io (IOVect len elem)
fromVect {len} vect = do
	vect' <- newVect
	case len of
		Z => pure ()
		S _ => copyFrom vect vect' 0
	pure vect'
	where
		copyFrom : {len : Nat} -> (src : Vect m elem) -> (dest : IOVect len elem) -> (pos : Fin len) -> io ()
		copyFrom [] dest _ = pure ()
		copyFrom (x :: xs) dest pos = do
			writeVect dest pos x
			case (strengthen $ FS pos) of
				Nothing => pure ()
				Just next => copyFrom xs dest next

main : IO ()
main = do
	v1 <- (fromVect [1, 2, 3, 4])
	case !(readVect v1 3) of
		Nothing => pure ()
		Just x => printLn x
