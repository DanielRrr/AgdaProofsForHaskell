module IEL where

open import CategoryStructure
open import Product
open import Function
open import Coproduct
open import Negation

postulate consist : {K : Set → Set}{{k : Applicative K}}{A : Set} → K A → ¬ (¬ A)

theorem₁ : {K : Set → Set}{{k : Applicative K}}{A : Set} → K A → K (K A)
theorem₁ = pure

theorem₂ : {K : Set → Set}{{k : Applicative K}}{A : Set} → ¬ (K A) → K (¬ (K A))
theorem₂ = pure

multLemma₁ : {K : Set → Set}{{k : Applicative K}}{A B : Set} → K (A → (B → A × B)) → (K A → K (B → A × B))
multLemma₁ = _<*>_

multLemma₂ : {K : Set → Set}{{k : Applicative K}}{A B : Set} → (K A → K (B → A × B)) → (K A → (K B → K (A × B)))
multLemma₂ f x y = (f x) <*> y

multLemma₃ : {K : Set → Set}{{k : Applicative K}}{A B : Set} → K (A → (B → A × B)) → (K A → (K B → K (A × B)))
multLemma₃ = multLemma₂ ∘ multLemma₁

mult : {K : Set → Set}{{k : Applicative K}}{A B : Set} → K A → (K B → K (A × B))
mult = multLemma₃ (pure _,_)

theorem₃ : {K : Set → Set}{{k : Applicative K}}{A B : Set} → (K A × K B) → K (A × B)
theorem₃ = curry mult

theorem₄ : {K : Set → Set}{{k : Applicative K}}{A B : Set} → K (A × B) → (K A × K B)
theorem₄ p = {!!} , {!!}
