sumToProd : Either (a × b) (a × c) → a × Either b c
sumToProd e = case e of λ where
  (Left  (x , y)) → x , Left  y
  (Right (x , z)) → x , Right z
