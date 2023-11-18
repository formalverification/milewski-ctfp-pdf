open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true; _∧_)
open import Data.String using (String)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_)
open import Data.List
open import Relation.Binary.PropositionalEquality

variable a b c : Set

swap : (a × b) → (b × a)
swap (x , y) = y , x

alpha : ((a × b) × c) → (a × (b × c))
alpha ((x , y) , z) = x , (y , z)

alpha_inv : (a × (b × c)) → ((a × b) × c)
alpha_inv (x , (y , z)) = (x , y) , z

rho : (a × ⊤) → a
rho (a , tt) = a

rho_inv : a → (a × ⊤)
rho_inv x = x , tt

module snippet9 where
  data Pair (a b : Set) : Set where
    P : a → b → Pair a b

  stmt : Pair String Bool
  stmt = P "This statement is" false

data Pair (a b : Set) : Set where
  pair : a → b → Pair a b

module snippet12 where
  stmt : String × Bool
  stmt = _,_ "This statement is" false

data Stmt : Set where
  stmt : String → Bool → Stmt
