prodToSum : A × Either B C → Either (A × B) (A × C)
prodToSum (x , Left y)  = Left (x , y)
prodToSum (x , Right z) = Right (x , z)
