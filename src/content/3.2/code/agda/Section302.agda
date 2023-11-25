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

{- Haskell https://hackage.haskell.org/package/comonad-5.0.8/docs/Control-Comonad.html -}
record RawComnad (w : Set → Set) : Set₁ where
  field
    {- snippet 03  -}
    extract : w c → a
    duplicate : w a → w (w b)
    extend : (w a → b) → w a → w b
