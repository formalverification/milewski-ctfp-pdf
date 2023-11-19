open import Data.String
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Function
private variable a b c : Set

Writer : Set -> Set
Writer a = a × String

morphism : a -> Writer b
morphism = {!   !}

_>=>_ : (a -> Writer b) -> (b -> Writer c) -> (a -> Writer c)
_>=>_ {c = c} m1 m2 x = (z , s)
  where
  z : c
  z = fst (m2 $ fst (m1 x))
  s : String
  s = snd (m1 x) ++ snd (m2 $ fst (m1 x))


return : a -> Writer a
return x = (x , "")
