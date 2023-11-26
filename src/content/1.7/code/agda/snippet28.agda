instance
  constFunc : Functor (Const C)
  constFunc .fmap = λ f → λ where (mkConst C) → mkConst C
