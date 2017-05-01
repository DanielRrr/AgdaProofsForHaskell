module UnitAndEmpty where

open import Function

data Unit : Set where
  ⊤ : Unit

data ⊥ : Set where

elim⊥ : {A : Set} → ⊥ → A
elim⊥()

¬ : Set → Set
¬ A = A → ⊥


contradiction : ∀ {A B} → A → (¬ A → B)
contradiction x ¬x = elim⊥(¬x x)

contraposition : ∀ {A B} → (A → B) → (¬ B → ¬ A)
contraposition = flip _∘′_

contraposition¬ : ∀ {A B} → (A → ¬ B) → (B → ¬ A)
contraposition¬ = flip

double : ∀ {A} → A → ¬ (¬ A)
double = contradiction

brower : ∀ {A} → ¬ (¬ (¬ A)) → ¬ A
brower f = f ∘ contradiction
