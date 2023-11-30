instance
  andBifunc : Bifunctor _×_
  andBifunc .bimap = λ f g (x , y) → f x , g y
