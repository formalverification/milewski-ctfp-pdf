_isPrefixOf_ : String → String → Bool

startsWithSymbol : Element → Bool
startsWithSymbol e = symbol e isPrefixOf name e
