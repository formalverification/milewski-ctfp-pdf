instance
  readerFunctor : Functor (Reader E)
  readerFunctor .fmap f (reader g) = reader (f ∘ g)
