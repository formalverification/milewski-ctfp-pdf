open import Data.Bool using (Bool)
open import Data.Product using (_×_)
open import Data.Float
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable A B C : Set

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

id : A → A
id x = x

fmap : (A → B) → Maybe A → Maybe B
fmap _ Nothing = Nothing
fmap f (Just x) = Just (f x)

fmap-id-lemma : ∀ x → (fmap{B = A} id) x ≡ id x
fmap-id-lemma Nothing = refl
fmap-id-lemma (Just x) = refl

fmap-∘-lemma :  ∀{f : A → B}{g : B → C}
  →             (x : Maybe A) → fmap (g ∘ f) x ≡ (fmap g ∘ fmap f) x
fmap-∘-lemma Nothing = refl
fmap-∘-lemma (Just x) = refl

record Eq (A : Set) : Set where
  field _==_ : A → A → Bool

data Point : Set where
  Pt : Float → Float → Point

instance
  _ : Eq Point
  _ = record { _==_ = λ x y → {!!} }
    where
    ξ : Point → Point → Bool
    ξ (Pt x₁ x₂) (Pt y₁ y₂) = {!(x₁ ≟ y₁) × (x₂ ≟ y₂)!}
