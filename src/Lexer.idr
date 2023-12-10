module Lexer

import Control.Relation.Erased as E
import Data.DPair
import Data.Erased
import Data.List
import Data.Nat
import Data.Vect

%default total

-- interface IndexedView ty where
--   Nil : {0 a : Type} -> ty Z a
--   (::) : a -> ty n a -> ty (S n) a

-- IndexedView Vect where
--   Nil = Nil
--   x :: xs = x :: xs

data View : {ty : Nat -> Type -> Type} -> ty n a -> Type where
  Nil : {nil : ty Z a} -> View {ty} nil
  (::) : {cons : a -> ty n a -> ty (S n) a} -> (x : a) -> (xs : ty n a) -> View {ty} (cons x xs)

-- view : (xs : Vect n a) -> View {ty = Vect} xs
-- view [] = []
-- view (x :: xs) = (::) {cons = (::)} x xs

public export
(:->) : (Nat -> Type) -> (Nat -> Type) -> (Nat -> Type)
(:->) a b n = a n -> b n

infixr 1 :->

public export
I : (Nat -> Type) -> Type
I a = {n : Nat} -> a n

export
record Box (a : Nat -> Type) (n : Nat) where
  constructor MkBox
  call : {m : Nat} -> (0 _ : m `LT` n) -> a m

restrictBoxLTE : {m, n : Nat} -> (0 _ : m `LTE` n) -> Box a n -> Box a m
restrictBoxLTE lte b = MkBox $ \lt => call b $ E.transitive lt lte

restrictBoxLT : {m, n : Nat} -> (0 _ : m `LT` n) -> Box a n -> Box a m
restrictBoxLT lt = restrictBoxLTE (lteSuccLeft lt)

export
map : ({n : Nat} -> a n -> b n) -> ({n : Nat} -> Box a n -> Box b n)
map f a = MkBox $ \lt => f $ call a lt

export
extract : ({n : Nat} -> Box a n) -> ({n : Nat} -> a n)
extract a = call a E.reflexive

export
duplicate : {n : Nat} -> Box a n -> Box (Box a) n
duplicate a = MkBox $ \lt => restrictBoxLT lt a

export
app : {n : Nat} -> Box (a :-> b) n -> Box a n -> Box b n
app f a = MkBox $ \lt => call f lt $ call a lt

0 uninhabited : Uninhabited t => (0 _ : t) -> Void
uninhabited x = Prelude.uninhabited x

fromLteSucc : (0 _ : LTE (S m) (S n)) -> Erased (LTE m n)
fromLteSucc (LTESucc lte) = Erase lte

export
fixBox : (0 a : Nat -> Type) -> ({n : Nat} -> Box a n -> a n) -> ({n : Nat} -> Box a n)
fixBox a f = go n
  where
    go : (n : Nat) -> Box a n
    go  Z    = MkBox $ \lt => void $ Lexer.uninhabited lt
    go (S n) = MkBox $ \lt =>
      let lte = Lexer.fromLteSucc lt
      in f $ MkBox $ \lt => call (go n) (E.transitive lt lte.value)

export
fix : (0 a : Nat -> Type) -> ({n : Nat} -> Box a n -> a n) -> ({n : Nat} -> a n)
fix _ f = extract $ fixBox _ f

public export
record Success (a : Type) (n : Nat) where
  constructor MkSuccess
  value : a
  {size : Nat}
  0 lt : size `LT` n
  leftover : Vect size Char

lteLift : {m, n : Nat} -> (0 _ : m `LTE` n) -> Success a m -> Success a n
lteLift lte = { lt $= flip transitive lte }

ltLift : {m, n : Nat} -> (0 _ : m `LT` n) -> Success a m -> Success a n
ltLift lt = lteLift $ lteSuccLeft lt

public export
record Parser (a : Type) (n : Nat) where
  constructor MkParser
  run : {m : Nat} -> (0 _ : m `LTE` n) -> Vect m Char -> List (Success a m)

export
sat : {n : Nat} -> Char -> Parser Char n
sat c = MkParser run
  where
    run : {m : Nat} -> (0 _ : m `LTE` n) -> Vect m Char -> List (Success Char m)
    run _ [] = empty
    run _ (x :: xs) =
      if c == x
      then pure $ MkSuccess c E.reflexive xs
      else empty

export
anyChar : {n : Nat} -> Parser Char n
anyChar = MkParser run
  where
    run : {m : Nat} -> (0 _ : m `LTE` n) -> Vect m Char -> List (Success Char m)
    run _ [] = empty
    run _ (x :: xs) = pure $ MkSuccess x E.reflexive xs

export
guardM : {n : Nat} -> (a -> Maybe b) -> Parser a n -> Parser b n
guardM f p = MkParser run
  where
    run : {m : Nat} -> (0 _ : m `LTE` n) -> Vect m Char -> List (Success b m)
    run lte xs =
      let
        x = p.run lte xs
      in mapMaybe (\y =>
          case f y.value of
            Nothing => Nothing
            Just value' => Just $ {value := value'} y
        ) x

export
(<$>) : {n : Nat} -> (a -> b) -> Parser a n -> Parser b n
(<$>) f p = MkParser $ \lte, xs => {value $= f} <$> run p lte xs

export
(<$) : {n : Nat} -> b -> Parser a n -> Parser b n
(<$) b p = const b <$> p

export
($>) : {n : Nat} -> Parser a n -> b -> Parser b n
($>) p b = const b <$> p

export
ignore : {n : Nat} -> Parser a n -> Parser () n
ignore p = p $> ()

export
fail : {n : Nat} -> Parser a n
fail = MkParser $ \_, _ => []

export
(<|>) : {n : Nat} -> Parser a n -> Parser a n -> Parser a n
(<|>) p1 p2 = MkParser $ \lte, xs => run p1 lte xs <|> run p2 lte xs

export
box : {n : Nat} -> Parser a n -> Box (Parser a) n
box p =
  MkBox $ \lt =>
    MkParser $ \lte, xs =>
      run p (E.transitive lte $ lteSuccLeft lt) xs

-- LChain : Type -> Nat -> Type
-- LChain a n = Success a n -> Box (Parser (a -> a)) n -> List (Success a n)

-- schainl : {n : Nat} -> LChain a n
-- schainl {a} = fix $ \rec, sa, op => aux rec sa op <|> pure sa
--   where
--     aux : {m : Nat} -> Box (LChain a) m -> LChain a m
--     aux rec success@(MkSuccess val lt xs) op = do
--       let op' = call op lt
--       sop <- run op' E.reflexive xs
--       let sa' = MkSuccess (sop.value val) sop.lt sop.leftover
--       res <- call rec lt sa' (restrictBoxLT lt op)
--       pure $ ltLift lt res

-- iterate : {n : Nat} -> Parser a n -> Box (Parser (a -> a)) n -> Parser a n
-- iterate p bpf = MkParser $ \lte, xs => do
--   x <- run p lte xs
--   schainl x $ restrictBoxLTE lte bpf

export
(:<?&>) : {n : Nat} -> Parser a n -> Parser b n -> Parser (Maybe a, b) n
(:<?&>) p1 p2 = MkParser $ \lte, xs =>
  let
    left = do
      MkSuccess val lt xs' <- run p1 lte xs
      MkSuccess val' lt' xs'' <- run p2 (E.transitive (lteSuccLeft lt) lte) xs'
      pure $ MkSuccess (Just val, val') (E.transitive lt' $ lteSuccLeft lt) xs''
    right : Lazy _ := do
      MkSuccess val lt xs' <- run p2 lte xs
      pure $ MkSuccess (Nothing, val) lt xs'
  in left <|> right

infixr 1 :<?&>

export
(&>>=*) : {0 b : a -> Type} -> {n : Nat} -> Parser a n -> Lazy ((x : a) -> Box (Parser (b x)) n) -> Parser (x : a ** b x) n
(&>>=*) p pf = MkParser $ \lte, xs => do
  MkSuccess x lt xs <- run p lte xs
  MkSuccess y lt' xs <- run (call (pf x) (E.transitive lt lte)) E.reflexive xs
  pure $ MkSuccess (x ** y) (E.transitive lt' $ lteSuccLeft lt) xs

infix 1 &>>=*

export
(&>>=) : {n : Nat} -> Parser a n -> (a -> Box (Parser b) n) -> Parser (a, b) n
(&>>=) p pf = MkParser $ \lte, xs => do
  MkSuccess x lt xs <- run p lte xs
  MkSuccess y lt' xs <- run (call (pf x) (E.transitive lt lte)) E.reflexive xs
  pure $ MkSuccess (x, y) (E.transitive lt' $ lteSuccLeft lt) xs

infix 1 &>>=

export
(>>=) : {n : Nat} -> Parser a n -> (a -> Box (Parser b) n) -> Parser b n
(>>=) p f = snd <$> (p &>>= f)

export
(>>) : {n : Nat} -> Parser a n -> Box (Parser b) n -> Parser b n
(>>) p1 p2 = p1 >>= const p2

export
(&?>>=*) : {0 b : a -> Type} -> {n : Nat} -> Parser a n -> ((x : a) -> Box (Parser (b x)) n) -> Parser (x : a ** Maybe (b x)) n
(&?>>=*) p pf = MkParser $ \lte, xs => do
  MkSuccess x lt xs <- run p lte xs
  let
    left = do
      MkSuccess y lt' xs <- run (call (pf x) (E.transitive lt lte)) E.reflexive xs
      pure $ MkSuccess (x ** Just y) (E.transitive lt' $ lteSuccLeft lt) xs
  left <|> pure (MkSuccess (x ** Nothing) lt xs)

infixl 1 &?>>=*

export
(&?>>=) : {n : Nat} -> Parser a n -> (a -> Box (Parser b) n) -> Parser (a, Maybe b) n
(&?>>=) p pf = MkParser $ \lte, xs => do
  MkSuccess x lt xs <- run p lte xs
  let
    left = do
      MkSuccess y lt' xs <- run (call (pf x) (E.transitive lt lte)) E.reflexive xs
      pure $ MkSuccess (x, Just y) (E.transitive lt' $ lteSuccLeft lt) xs
  left <|> pure (MkSuccess (x, Nothing) lt xs)

infix 10 &?>>=

export
(<*>) : {n : Nat} -> Parser (a -> b) n -> Box (Parser a) n -> Parser b n
(<*>) pf p = MkParser $ \lte, xs => do
  MkSuccess f lt xs <- run pf lte xs
  MkSuccess x lt' xs <- run (call p (E.transitive lt lte)) E.reflexive xs
  pure $ MkSuccess (f x) (E.transitive lt' $ lteSuccLeft lt) xs

export
(<*) : {n : Nat} -> Parser a n -> Box (Parser b) n -> Parser a n
(<*) p1 p2 = (const <$> p1) <*> p2

export
(*>) : {n : Nat} -> Parser a n -> Box (Parser b) n -> Parser b n
(*>) p1 p2 = (flip const <$> p1) <*> p2

export
(<*?>) : {n : Nat} -> Parser (a -> b) n -> Box (Parser a) n -> Parser (Maybe b) n
(<*?>) p1 p2 = uncurry map <$> (p1 &?>>= const p2)

infixl 3 <*?>

export
(*?>) : {n : Nat} -> Parser a n -> Box (Parser b) n -> Parser (Maybe b) n
(*?>) p1 p2 = (flip const <$> p1) <*?> p2

infixl 3 *?>

export
(?&>>=) : {n : Nat} -> Parser a n -> (Maybe a -> Parser b n) -> Parser (Maybe a, b) n
(?&>>=) p1 p2 = (p1 >>= \x => (box $ (Just x,) <$> (p2 $ Just x))) <|> ((Nothing,) <$> p2 Nothing)

infixl 1 ?&>>=

export
(<?*>) : {n : Nat} -> Parser (a -> a) n -> Parser a n -> Parser a n
(<?*>) f p = (uncurry $ flip applyMaybe) <$> (f ?&>>= const p)
  where
    applyMaybe x = fromMaybe x . map (flip apply x)

infixl 3 <?*>

export
(?*>) : {n : Nat} -> Parser a n -> Parser b n -> Parser b n
(?*>) p1 p2 = snd <$> (p1 ?&>>= const p2)

infixl 3 ?*>

public export
(<&>) : {n : Nat} -> Parser a n -> Box (Parser b) n -> Parser (a, b) n
(<&>) p1 p2 = ((,) <$> p1) <*> p2

infixl 3 <&>

export
(<&?>) : {n : Nat} -> Parser a n -> Box (Parser b) n -> Parser (a, Maybe b) n
(<&?>) p1 p2 = p1 &?>>= const p2

infixl 3 <?&>

export
(<?&>) : {n : Nat} -> Parser a n -> Parser b n -> Parser (Maybe a, b) n
(<?&>) p1 p2 = p1 ?&>>= const p2

infixl 3 <&?>

export
some : {0 a : Type} -> I (Parser a :-> Parser (Subset (List a) NonEmpty))
some = fix (Parser a :-> Parser (Subset (List a) NonEmpty)) $ \rec, p =>
  f <$> (p <&?> (app rec $ box p))
where
  f : (a, Maybe $ Subset (List a) NonEmpty) -> Subset (List a) NonEmpty
  f (x, Nothing) = Element [x] IsNonEmpty
  f (x, Just xs) = case xs of
    Element (y :: ys) _ => Element (x :: y :: ys) IsNonEmpty
