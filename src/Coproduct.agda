module Coproduct where 

open import Function
open import Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

data _+_ (P Q : Set) : Set where
  inl : P → P + Q
  inr : Q → P + Q

elim∨ : {P Q R : Set} → (P → R) → (Q → R) → (P + Q → R)
elim∨ f g (inl x) = f x
elim∨ f g (inr x) = g x

infixr 1 _+_

∨-assoc₁ : {P Q R : Set} → P + (Q + R) → (P + Q) + R
∨-assoc₁ (inl x) = inl (inl x)
∨-assoc₁ (inr (inl x)) = inl (inr x)
∨-assoc₁ (inr (inr x)) = inr x

∨-assoc₂ : {P Q R : Set} → (P + Q) + R → P + (Q + R)
∨-assoc₂ (inl (inl x)) = inl x
∨-assoc₂ (inl (inr x)) = inr (inl x)
∨-assoc₂ (inr x) = inr (inr x)

∨-assoc : {P Q R : Set} → P + (Q + R) ⇔ (P + Q) + R
∨-assoc = (∨-assoc₁ , ∨-assoc₂)

imdepotency-∨₁ : {P : Set} → P → P + P
imdepotency-∨₁ p = inl p

imdepotency-∨₂ : {P : Set} → P + P → P
imdepotency-∨₂ (inl x) = x
imdepotency-∨₂ (inr x) = x

imdepotency-∨ : {P : Set} → P ⇔ P + P
imdepotency-∨ = (imdepotency-∨₁ , imdepotency-∨₂)
