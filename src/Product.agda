module Product where

open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 2 _×_

π₁ : ∀ {A B} → (A × B) → A
π₁ (x , x₁) = x

π₂ : ∀ {A B : Set} → (A × B) → B
π₂ (x , x₁) = x₁

curry : ∀ {A B C : Set} → (A → B → C) → A × B → C
curry f (x , y) = f x y

uncurry : ∀ {A B C : Set} → (A × B → C) → A → B → C
uncurry f x y = f (x , y)

×-fun : ∀ {A B C : Set} → (f : C → A)(g : C → B)(x : C) → A × B
×-fun f g x = (f x) , (g x)

uniProd₁ : ∀ {A B C : Set} → (f : C → A)(g : C → B)(x : C) → (π₁ (×-fun f g x)) ≡ f x 
uniProd₁ f g x = refl

uniProd₂ : ∀ {A B C : Set} → (f : C → A)(g : C → B)(x : C) → (π₂ (×-fun f g x)) ≡ g x
uniProd₂ f g x = refl
