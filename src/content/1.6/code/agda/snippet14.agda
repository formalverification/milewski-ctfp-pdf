startsWithSymbol : (String × String × ℤ) → Bool
startsWithSymbol (name , symbol , _) = isPrefixOf symbol name
