sumToProd : Either (A × B) (A × C) → A × Either B C
sumToProd e = case e of λ where
  (Left  (x , y)) → x , Left  y
  (Right (x , z)) → x , Right z

-- or, alternatively,
sumToProd' : Either (A × B) (A × C) → A × Either B C
sumToProd' (Left  (x , y)) = x , Left  y
sumToProd' (Right (x , z)) = x , Right z
