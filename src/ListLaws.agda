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
applicativeList = mkApplicative pure _<*>_  pure-id <*>-∘ hom_law app_pure_law where
  pure : ∀ {A} → A → List A
  pure x = x ∷ []

  _<*>_ : ∀ {A B} → List (A → B) → List A → List B
  [] <*> xs = []
  (f ∷ fs) <*> xs = map f xs ++ fs <*> xs

  pure-id : ∀ {A} → (fx : List A) → ((pure id) <*> fx) ≡ fx
  pure-id [] = refl
  pure-id (x ∷ xs) = cong (_∷_ x) (pure-id xs)

  <*>-∘ : ∀ {A B C} → (f : List (B → C))(g : List (A → B))(x : List A) → (((pure (λ f g → f ∘ g) <*> f) <*> g) <*> x) ≡ (f <*> (g <*> x))
  <*>-∘ [] g x = refl
  <*>-∘ (f ∷ fs) [] x = cong (map f) refl
  <*>-∘ (f ∷ fs) (g ∷ gs) xs = cong (map (f ∘ g)) refl
  
  hom_law : ∀ {A B}(f : A → B)(x : A) → (pure f <*> pure x) ≡ pure (f x)
  hom_law f x = refl

  app_pure_law : ∀ {A B}(f : List (A → B))(x : A) → (f <*> pure x) ≡ (pure (λ f → f $ x) <*> f)
  app_pure_law [] x = refl
  app_pure_law (f ∷ fs) x = cong (_∷_ (f x)) (app_pure_law fs x)

kleisliList : KleisliTriple List
kleisliList = {!!}
