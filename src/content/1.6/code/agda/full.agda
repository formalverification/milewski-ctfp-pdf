open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

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
