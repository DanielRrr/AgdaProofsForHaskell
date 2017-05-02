module ListLaws where

open import CategoryStructure
open import AlgebraStructures
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)
open import Function
open import Data.List

functorList : Functor List
functorList = mkFunctor fmap fmap-id fmap-∘ where
  fmap : ∀ {A B} → (A → B) → List A → List B
  fmap f [] = []
  fmap f (x ∷ x₁) = (f x) ∷ fmap f x₁

  fmap-id : {A : Set}(fx : List A) → fmap id fx ≡ id fx
  fmap-id [] = refl
  fmap-id (x ∷ xs) = cong (_∷_ x) (fmap-id xs)

  fmap-∘ : {A B C : Set}{f : A → B}{g : B → C}(fx : List A) → fmap (g ∘ f) fx ≡ (fmap g ∘ fmap f) fx
  fmap-∘ [] = refl
  fmap-∘ {f = f}{g} (x ∷ xs) = cong (_∷_ (g (f x))) (fmap-∘ xs)

monoidList : ∀ {A} → Monoid (List A)
monoidList = mkMonoid ε _●_  ε-unit₁  ε-unit₂ assoc-Monoid where
  ε : ∀ {A} → List A
  ε = []

  _●_ : ∀ {A} → List A → List A → List A
  [] ● xs = xs
  (x ∷ xs) ● ys = x ∷ (xs ● ys)

  ε-unit₁ : ∀ {A} → (x : List A) → (x ● []) ≡ x
  ε-unit₁ [] = refl
  ε-unit₁ (x ∷ xs) = cong (_∷_ x) (ε-unit₁ xs)
  
  ε-unit₂ : ∀ {A} → (x : List A) → x ≡ (x ● [])
  ε-unit₂ [] = refl
  ε-unit₂ (x ∷ xs) = cong (_∷_ x) (ε-unit₂ xs)
  
  assoc-Monoid : ∀ {A} → (x y z : List A) → ((x ● y) ● z) ≡ (x ● (y ● z))
  assoc-Monoid [] ys zs = refl
  assoc-Monoid (x ∷ xs) ys zs = cong (_∷_ x) (assoc-Monoid xs ys zs)

applicativeList : Applicative List
applicativeList = mkApplicative {!!} {!!} {!!} {!!} {!!} {!!}


kleisliList : KleisliTriple List
kleisliList = {!!}
