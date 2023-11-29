BiComp : Bifunctor BF → Functor F → Functor G → Set → Set → Set
BiComp bf fu gu a b = bf ⟨$⟩ (fu $ a , gu $ b)
  where
  _$_ : ∀{F} → Functor F → Set → Set
  _$_ {F} f A = F A

  _⟨$⟩_ : ∀{BF} → Bifunctor BF → Set × Set → Set
  _⟨$⟩_ {BF} bf (a , b) = BF a b
