module Test.Lexer

import Data.DPair
import Data.List
import Data.String
import Data.String.AsVect
import Data.Vect
import Data.Vect.Lazy
import Lexer

%hide Prelude.Ops.infixl.(<&>)

%default total

digit : {n : Nat} -> Parser Nat n
digit = foldr1 (<|>) opts
  where
    opts : List (Parser Nat n)
    opts =
      [ 0 <$ sat '0'
      , 1 <$ sat '1'
      , 2 <$ sat '2'
      , 3 <$ sat '3'
      , 4 <$ sat '4'
      , 5 <$ sat '5'
      , 6 <$ sat '6'
      , 7 <$ sat '7'
      , 8 <$ sat '8'
      , 9 <$ sat '9'
      ]

nat : {n : Nat} -> Parser Nat n
nat = reduce <$> some digit
  where
    reduce : Subset (List Nat) NonEmpty -> Nat
    reduce (Element xs _) =
      foldl1 (\acc, elem => acc * 10 + elem) xs

signed : Neg a => {n : Nat} -> Parser a n -> Parser a n
signed p = sat '-' $> negate <?*> p

int : {n : Nat} -> Parser Int n
int = signed $ cast <$> nat

decimal : {n : Nat} -> Parser Double n
decimal =
  let
    left = reduceLeft <$> some digit
    right = reduceRight <$> some digit
    leftRight = left <&> (box $ sat '.' *> box right)
    combine = uncurry (+)
    unsigned = combine <$> leftRight
  in signed unsigned
  where
    reduceLeft : Subset (List Nat) NonEmpty -> Double
    reduceLeft (Element xs _) =
      foldl (\acc, elem => acc * 10 + cast elem) (the Double 0) xs

    reduceRight : Subset (List Nat) NonEmpty -> Double
    reduceRight (Element xs _) =
      foldl (\acc, elem => acc / 10 + cast elem / 10) (the Double 0) . reverse $ xs

parens : {n : Nat} -> Parser () n
parens = fix (Parser ()) $ \rec =>
  const () <$> some ((sat '(' *> rec <|> (const () <$> (sat '(' *> box decimal))) <* (box $ sat ')'))

namespace ListView
  public export
  interface HasNil a ty where
    nil : ty Z a

  public export
  interface HasCons a ty where
    cons : a -> ty n a -> ty (S n) a

  public export
  data ListView : (HasNil a ty, HasCons a ty) => ty n a -> Type where
    Nil : (HasNil a ty, HasCons a ty) => ListView {a} {ty} (nil {a} {ty})
    (::) : (HasNil a ty, HasCons a ty) => (x : a) -> (xs : ty n a) -> ListView {a} {ty} (cons x xs)

  public export
  interface (HasNil a ty, HasCons a ty) => HasListView a ty where
    view : (xs : ty n a) -> ListView {a} {ty} xs

data HasLength : Nat -> String -> Type where
  Z : HasLength Z ""
  S : HasLength n str -> HasLength (S n) (strCons c str)

HasNil a Vect where
  nil = Nil

HasCons a Vect where
  cons = (::)

HasListView a Vect where
  view [] = Nil
  view (x :: xs) = x :: xs

strToLazyVect : (str : String) -> LazyVect (length str) Char
strToLazyVect str = go $ asVect str
  where
    go : AsVect str1 m -> LazyVect m Char
    go [] = []
    go (x :: xs) = x :: go xs

data AST = IntLit Int | DoubleLit Double | Add AST AST

Show AST where
  show (IntLit x) = show x
  show (DoubleLit x) = show x
  show (Add x y) =
    let
      x : String := case x of { IntLit _ => show x ; DoubleLit _ => show x ; Add _ _ => "(\{show x})" }
      y : String := case y of { IntLit _ => show y ; DoubleLit _ => show y ; Add _ _ => "(\{show y})" }
    in "+ \{x} \{y}"

between : {n : Nat} -> Char -> Char -> Box (Parser a) n -> Parser a n
between c1 c2 p = sat c1 *> p <* box (sat c2)

ast : {n : Nat} -> Parser AST n
ast = fix (Parser AST) $ \rec => add rec <|> DoubleLit <$> decimal <|> IntLit <$> int
  where
    inParens : {m : Nat} -> Box (Parser a) m -> Parser a m
    inParens p = between '(' ')' p

    add : {m : Nat} -> Box (Parser AST) m -> Parser AST m
    add rec = inParens . box $ (Add <$> (sat '+' *> box (sat ' ') *> rec)) <*> box (sat ' ' *> rec)

eval : AST -> Either Double Int
eval (IntLit x) = Right x
eval (DoubleLit x) = Left x
eval (Add x y) = case (eval x, eval y) of
  (Right x, Right y) => Right $ x + y
  (Right x, Left y) => Left $ cast x + y
  (Left x, Right y) => Left $ x + cast y
  (Left x, Left y) => Left $ x + y

export
main : IO Bool
main = do
  -- putStrLn "Generating string..."
  -- let
  --   str = replicate 500000 '!'
  -- putStrLn "Starting..."
  -- let
  --   xs : (n : Nat ** LazyVect n Char) := (length str ** strToLazyVect str)
  -- putStrLn $ case xs of { (Z ** []) => "" ; (S _ ** xs@(x :: _)) => singleton x }

  putStr "> "
  input <- getLine
  case input of
    ":q" => pure True
    input => main' input $> False
  where
    main' : String -> IO ()
    main' input = do
      let
        xs : List (Success _ _) := run ast reflexive $ fromList $ unpack input
        xs = map (\(MkSuccess x _ rest) => (x, pack . toList $ rest)) xs
      case xs of
        [] => putStrLn "Parse failure"
        x :: _ => printLn $ mapFst eval x
