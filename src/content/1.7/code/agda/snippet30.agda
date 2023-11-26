open import Agda.Builtin.Int
open import Data.Integer

square : Int → Int
square x = x * x

mis : Maybe (List Int)
mis = Just (+ 1 ∷ + 2 ∷ + 3 ∷ [])

instance
  ListFunc : Functor List
  ListFunc .fmap _ [] = []
  ListFunc .fmap f (x ∷ as) = (f x) ∷ (fmap f as)

mis2 : Maybe (List Int)
mis2 = fmap (fmap square) mis
