open import Agda.Builtin.Int
open import Data.Integer

instance
  ListFunc : Functor List
  ListFunc .fmap _ [] = []
  ListFunc .fmap f (x ∷ as) = (f x) ∷ (fmap f as)
