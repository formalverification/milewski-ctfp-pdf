open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

variable A B a b c d x : Set

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
    extract : w c → c
    duplicate : w a → w (w b)
    extend : (w a → b) → w a → w b

{- from section about Functors 7 -}
record Functor (f : Set → Set) : Set₁ where
  field fmap : (a → b) → f a → f b

{- from section about Representable functors 2.4 -}
record Representable (f : Set → Set) : Set₁ where
  field
    Repf      : Set
    tabulate  : (Repf → x) → f x
    index     : f x → Repf → x

record RawAdjunction (f : Set → Set) (u : Set → Set)
    ⦃ _ : Functor u ⦄
    ⦃ _ : Representable u ⦄ : Set₁ where
  field
    {- snippet 04 -}
    unit : a → u (f a)
    counit : f (u a) → a
