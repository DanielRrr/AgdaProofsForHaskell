module Equality where

infix 4 _≡_
data _≡_ {α}{A : Set α}(x : A) : A → Set where
  refl : x ≡ x

cong : ∀ {α}{A B : Set α}{a b : A} → (f : A → B) → (a ≡ b) → (f a ≡ f b)
cong f refl = refl
