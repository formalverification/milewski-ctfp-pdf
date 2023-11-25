open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

variable A B a b d : Set

{- snippet 01 - defined in Data.Product.Base -}
swap : A × B → B × A
swap (x , y) = (y , x)

{- Haskell https://hackage.haskell.org/package/base-4.19.0.0/docs/Control-Monad.html#t:Monad -}
record RawMonad (m : Set → Set) : Set₁ where
  field
    {- snippet 02  -}
    return : d → m d
    _>>=_  : m a → (a → m b) → m b
