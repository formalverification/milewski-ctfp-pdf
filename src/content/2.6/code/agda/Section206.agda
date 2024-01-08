{- 16 Yoneda Embedding -----------------------------------------------------------}

module Section206 where
open import Function using (id)
private variable a b x : Set

{- 16.2 Application to Haskell ---------------------------------------------------}
module snippet01 {btoa : b → a} where
  {-                                                                 [snippet01] -}
  fromY : (a → x) → b → x
  fromY f b = f (btoa b)
  {-                                                                 [snippet02] -}
  _ : b → a
  _ = fromY id
