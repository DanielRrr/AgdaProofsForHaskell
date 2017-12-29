{-# OPTIONS --allow-unsolved-metas #-}

module Modules where

open import Ring
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function
open import Monoid
open import Group

record Left-R-Module (A : Set)(B : Set){{R : Ring A}}{{AR : AssociativeRing A}}{{O : RingWithOne A}}{{M : Monoid B}}{{G : Group B}}{{Ab : Abelian B}} : Set where
  constructor mkLeft-R-Module
  infixr 8 _··_
  field
    _··_ : A → B → B
    axiom₁ : (r s : A) → (a : B) → ((r + s) ·· a) ≡ ((r ·· a) ● (s ·· a))
    axiom₂ : (r s : A) → (a : B) → ((r · s) ·· a) ≡ (r ·· (s ·· a))
    axiom₃ : (r : A) → (a b : B) → (r ·· (a ● b)) ≡ ((r ·· a) ● (r ·· b))
    axiom₄ : (a : B) → Ε ·· a ≡ a
open Left-R-Module {{...}} public
