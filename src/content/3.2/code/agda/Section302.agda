open import Data.Product using (_×_; _,_)

variable A B : Set

{- snippet 01 - defined in Data.Product.Base -}
swap : A × B → B × A
swap (x , y) = (y , x)
