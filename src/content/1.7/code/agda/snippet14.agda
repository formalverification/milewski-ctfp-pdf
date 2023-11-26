instance  _ : Functor Maybe
          _ = record  { Fmap = λ f → λ where
                          Nothing → Nothing
                          (Just a) → Just (f a)
                      }
