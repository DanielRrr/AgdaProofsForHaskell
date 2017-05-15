open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning

module Geometry where

Point = Set

data PDP (A B : Point) : Set where
  _,_ : A → B → PDP A B

fst : {A B : Point} → PDP A B → A
fst (x , x₁) = x

snd : {A B : Point} → PDP A B → B
snd (x , x₁) = x₁

data Line (A B : Point) : Set where
  line : PDP A B → Line A B

data Plane (A B C : Point) : Set where
  plane : PDP A (PDP B C) → Plane A B C

lineToPlane : {A B C : Point} → Line A B → Line B C → Plane A B C
lineToPlane (line (x , x₁)) (line x₂) = plane (x , x₂)

lineElim : {A B : Point} → Line A B → PDP A B
lineElim (line (x , x₁)) = x , x₁

planeElim : {A B C : Point} → Plane A B C → PDP A (PDP B C)
planeElim (plane (x , x₁)) = x , x₁

record Circle : Set₁ where
  constructor mkCircle
  field
    base : ∀ {A : Point} → A
    radius : ∀ {A : Point}{B : Point} → Line A B
open Circle {{...}} public


record Functor (F : Set → Set) : Set₁ where
  constructor mkFunctor
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set}(fx : F A) → fmap id fx ≡ id fx
    fmap-∘ : {A B C : Set}(g : B → C)(f : A → B)(fx : F A) → fmap (g ∘ f) fx ≡ (fmap g ∘ fmap f) fx
open Functor {{...}} public


lineFmap : ∀ {A : Point} → Functor (Line A)
lineFmap = mkFunctor map map-id map-∘ where
  map : {A B C : Point} → (B → C) → Line A B → Line A C
  map f (line (x , x₁)) = line (x , f x₁)

  map-id : {A B : Point} (fx : Line A B) → map id fx ≡ id fx
  map-id (line (x , x₁)) = refl

  map-∘ : {A B C D : Point} (g : C → D) (f : B → C) (fx : Line A B) → map (g ∘ f) fx ≡ (map g ∘ map f) fx
  map-∘ g f (line (x , y)) = begin
        (map (g ∘ f) (line (x , y))
        ≡⟨ cong (map (g ∘ f)) refl ⟩
        refl)
