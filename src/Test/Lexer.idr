module Test.Lexer

import Data.DPair
import Data.List
import Data.Vect
import Lexer

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
    leftRight = left <&?> (box $ sat '.' *> box right)
    combine = uncurry $ \x => maybe x (x +)
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
parens {n} = fix (Parser ()) $ \rec =>
  const () <$> some ((sat '(' *> rec <|> (const () <$> (sat '(' *> box decimal))) <* (box $ sat ')'))

export
main : IO ()
main = do
  let
    xs : List (Success _ _) := run parens reflexive $ fromList $ unpack "(100.1)(100)"
    xs = map (\(MkSuccess x _ rest) => (x, pack . toList $ rest)) xs
  case xs of
    [] => putStrLn "Parse failure"
    x :: _ => printLn x
