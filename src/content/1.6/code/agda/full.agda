open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.String using (String; toList)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_)
open import Data.List as List
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
    open import Data.Bool using (Bool; false; true; _∧_)

    data Pair (a b : Set) : Set where
      P : a → b → Pair a b

    stmt : Pair String Bool
    stmt = P "This statement is" false

data Pair (a b : Set) : Set where
  pair : a → b → Pair a b

module snippet12 where
  open import Data.Bool using (Bool; false)
  stmt : String × Bool
  stmt = _,_ "This statement is" false

module snippet13 where
  open import Data.Bool using (Bool)

  data Stmt : Set where
    stmt : String → Bool → Stmt

record Element : Set where
  constructor element
  field name : String
        symbol : String
        atomicNumber : ℤ

tupleToElem : (String × String × ℤ) → Element
tupleToElem (n , s , a) = element s s a

elemToTuple : Element → (String × String × ℤ)
elemToTuple e = name e , (name e) , (atomicNumber e)
  where open Element

atomicNumber : Element -> ℤ
atomicNumber = Element.atomicNumber

data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b

data OneOfThree (a b c : Set) : Set where
  Sinistral : a → OneOfThree a b c
  Medial    : b → OneOfThree a b c
  Dextral   : c → OneOfThree a b c

snippet23 : Either a ⊥
snippet23 = {!   !}

data Color : Set where
  Red   : Color
  Green : Color
  Blue  : Color

module snippet25 where
  data Bool : Set where
    True False : Bool

data Maybe (a : Set) : Set where
  Nothing :     Maybe a
  Just    : a → Maybe a

data NothingType : Set where
  Nothing : NothingType

data JustType (a : Set) : Set where
  Just : a → JustType a
