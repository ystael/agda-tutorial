module Category where

open import Relation.Binary.Core using (_≡_)

record Category : Set1 where
  field
    Objects : Set
    Hom : (A B : Objects) → Set
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    ∘-assoc : ∀ {A B C D} → {f : Hom A B} → {g : Hom B C} → {h : Hom C D} →
              h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
    id : {A : Objects} → Hom A A
