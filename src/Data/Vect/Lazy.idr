module Data.Vect.Lazy

import public Data.Fin
import Data.Vect

%default total

public export
data LazyVect : Nat -> Type -> Type where
  Nil : LazyVect Z a
  (::) : (x : a) -> (xs : Lazy (LazyVect n a)) -> LazyVect (S n) a

public export
length : LazyVect n a -> Nat
length [] = Z
length (_ :: xs) = S (length xs)

export
lengthCorrect : (xs : LazyVect n a) -> length xs = n
lengthCorrect [] = Refl
lengthCorrect (_ :: xs) = rewrite lengthCorrect xs in Refl

public export
tail : LazyVect (S n) a -> LazyVect n a
tail (_ :: xs) = xs

public export
head : LazyVect (S n) a -> a
head (x :: _) = x

public export
last : LazyVect (S n) a -> a
last [x] = x
last (_ :: xs@(_ :: _)) = last xs

public export
init : LazyVect (S n) a -> LazyVect n a
init [x] = []
init (x :: xs@(_ :: _)) = x :: init xs

public export
take : (n : Nat) -> LazyVect (n + m) a -> LazyVect n a
take Z _ = []
take (S n) (x :: xs) = x :: take n xs

namespace Stream
  public export
  take : (n : Nat) -> Stream a -> LazyVect n a
  take Z _ = []
  take (S n) (x :: xs) = x :: take n xs

public export
drop : (n : Nat) -> LazyVect (n + m) a -> LazyVect m a
drop Z xs = xs
drop (S n) (_ :: xs) = drop n xs

public export
dropUpTo : (n : Nat) -> LazyVect m a -> LazyVect (m `minus` n) a
dropUpTo Z xs = rewrite minusZeroRight m in xs
dropUpTo (S n) [] = []
dropUpTo (S n) (_ :: xs) = dropUpTo n xs

public export
index : Fin len -> LazyVect len a -> a
index FZ (x :: _) = x
index (FS n) (_ :: xs) = index n xs

public export
insertAt : Fin (S n) -> a -> LazyVect n a -> LazyVect (S n) a
insertAt FZ y xs = y :: xs
insertAt (FS n) y (x :: xs) = x :: insertAt n y xs

public export
replicate : (n : Nat) -> a -> LazyVect n a
replicate Z _ = []
replicate (S n) x = x :: replicate n x

public export
foldr : (a -> Lazy acc -> acc) -> Lazy acc -> LazyVect n a -> acc
foldr _ acc [] = acc
foldr f acc (x :: xs) = f x $ foldr f acc xs

public export
(++) : LazyVect n a -> Lazy (LazyVect m a) -> LazyVect (n + m) a
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

public export
Eq a => Eq (LazyVect n a) where
  [] == [] = True
  x :: xs == y :: ys = x == y && xs == ys

public export
Ord a => Ord (LazyVect n a) where
  compare [] [] = EQ
  compare (x :: xs) (y :: ys) = case compare x y of
    EQ => compare xs ys
    ord => ord

public export
Foldable (LazyVect n) where
  foldr f init [] = init
  foldr f init (x :: xs) = f x $ Prelude.foldr f init xs

public export
concat : LazyVect m (LazyVect n a) -> LazyVect (m * n) a
concat [] = []
concat (x :: xs) = x ++ concat xs

public export
foldr1 : (a -> Lazy a -> a) -> LazyVect (S n) a -> a
foldr1 f [x] = x
foldr1 f (x :: xs@(_ :: _)) = f x $ foldr1 f xs

public export
foldl1 : (a -> a -> a) -> LazyVect (S n) a -> a
foldl1 f (x :: xs) = foldl f x xs

public export
Zippable (LazyVect n) where
  zipWith f [] [] = []
  zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

  zipWith3 f [] [] [] = []
  zipWith3 f (x :: xs) (y :: ys) (z :: zs) = f x y z :: zipWith3 f xs ys zs

  unzipWith f [] = ([], [])
  unzipWith f (x :: xs) =
    let
      (y, z) = f x
      (ys, zs) = unzipWith f xs
    in (y :: ys, z :: zs)

  unzipWith3 f [] = ([], [], [])
  unzipWith3 f (x :: xs) =
    let
      (y, z, w) = f x
      (ys, zs, ws) = unzipWith3 f xs
    in (y :: ys, z :: zs, w :: ws)

public export
intersperse : a -> LazyVect (S n) a -> LazyVect (S n + n) a
intersperse _ [x] = [x]
intersperse {n = S n} y (x :: xs@(_ :: _)) =
  rewrite sym $ plusSuccRightSucc n n in x :: y :: intersperse y xs

public export
Semigroup a => Semigroup (LazyVect n a) where
  (<+>) = zipWith (<+>)

public export
{n : Nat} -> Monoid a => Monoid (LazyVect n a) where
  neutral = replicate n neutral

public export
Functor (LazyVect n) where
  map _ [] = []
  map f (x :: xs) = f x :: map f xs

export
Show a => Show (LazyVect n a) where
  show [] = "[]"
  show xs@(_ :: _) = "[\{commaSep xs}]"
    where
      commaSep : LazyVect (S m) a -> String
      commaSep = foldl1 (++) . intersperse ", " . map show

public export
fromVect : Vect n a -> LazyVect n a
fromVect [] = []
fromVect (x :: xs) = x :: fromVect xs
