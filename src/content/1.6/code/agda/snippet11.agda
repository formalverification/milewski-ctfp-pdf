-- [Agda's Not Haskell!]
-- Agda prohibits using the same name for type and data constructors.
data Pair (A B : Set) : Set where
  pair : A → B → Pair A B
