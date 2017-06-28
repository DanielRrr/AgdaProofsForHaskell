module Negation where

open import Function

data ⊥ : Set where

elim⊥ : {A : Set} → ⊥ → A
elim⊥()

¬ : Set → Set
¬ A = A → ⊥

contradiction : {A B : Set} → A → (¬ A → B)
contradiction x ¬x = elim⊥(¬x x)

contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f g x = g (f x)

contraposition¬ : {A B : Set} → (A → ¬ B) → (B → ¬ A)
contraposition¬ = flip

double : {A : Set} → A → ¬ (¬ A)
double = contradiction

brower : {A : Set} → ¬ (¬ (¬ A)) → ¬ A
brower f = f ∘ contradiction
