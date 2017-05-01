module Product where

open import CategoryStructure

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 2 _×_

fst : ∀ {A B} → (A × B) → A
fst (x , x₁) = x

snd : ∀ {A B : Set} → (A × B) → B
snd (x , x₁) = x₁

curry : ∀ {A B C : Set} → (A → B → C) → A × B → C
curry f (x , y) = f x y

uncurry : ∀ {A B C : Set} → (A × B → C) → A → B → C
uncurry f x y = f (x , y)

