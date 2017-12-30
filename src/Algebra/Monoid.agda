module Monoid where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function
open import Data.Product
open import Data.Nat renaming (_+_ to _+ℕ_)

record Monoid (A : Set) : Set where
  constructor mkMonoid
  infixr 4 _●_
  field
    _●_ : A → A → A
    ε : A
    assoc : (x y z : A) → ((x ● y) ● z) ≡ (x ● (y ● z))
    ε-unit₁ : (x : A) → (x ● ε) ≡ x
    ε-unit₂ : (x : A) → (ε ● x) ≡ x

  neut-Prop : (a : A) → (a ● ε) ≡ (ε ● a)
  neut-Prop a = trans (ε-unit₁ a) (sym (ε-unit₂ a))

  mon-● : (a b c : A) → a ≡ b → (a ● c) ≡ (b ● c)
  mon-● a b c refl = refl

  mon-●₁ : (a b c : A) → a ≡ b → (c ● a) ≡ (c ● b)
  mon-●₁ a b c refl = refl

  infixr 7 _^^_

  _^^_ : A → ℕ → A
  x ^^ zero = ε
  x ^^ suc y = (x ^^ y) ● x

  ^^prop : (a : A) → (m n : ℕ) → m ≡ n → a ^^ m ≡ a ^^ n
  ^^prop a m n refl = refl

  plusZero : (n : ℕ) → n +ℕ zero ≡ n
  plusZero zero = refl
  plusZero (suc n) = begin
                   (suc n +ℕ zero
                   ≡⟨ refl ⟩
                   suc (n +ℕ zero)
                   ≡⟨ cong suc (plusZero n) ⟩
                   refl)

  expEq : (a : A) → (m n : ℕ) → (m ≡ n) → (a ^^ m) ≡ (a ^^ n)
  expEq a m n refl = refl

  postulate addProp : (m n : ℕ) → (m +ℕ suc n) ≡ (suc (m +ℕ n))
  

  expProp1 : (a : A) → (m n : ℕ) → ((a ^^ m) ● (a ^^ n)) ≡ (a ^^ (m +ℕ n))
  expProp1 a m zero = begin
                      (a ^^ m) ● (a ^^ zero)
                      ≡⟨ mon-●₁ (a ^^ zero) ε (a ^^ m) refl ⟩
                      (a ^^ m) ● ε
                      ≡⟨ ε-unit₁ (a ^^ m) ⟩
                      a ^^ m
                      ≡⟨ ^^prop a m (m +ℕ zero) (sym (plusZero m)) ⟩
                      refl
  expProp1 a m (suc n) = begin
                         (a ^^ m) ● (a ^^ (suc n)) 
                         ≡⟨ refl ⟩
                         (a ^^ m) ● (a ^^ n) ● a
                         ≡⟨ sym (assoc (a ^^ m) (a ^^ n) a) ⟩
                         ((a ^^ m) ● (a ^^ n)) ● a
                         ≡⟨ mon-● ((a ^^ m) ● (a ^^ n)) (a ^^ (m +ℕ n)) a (expProp1 a m n) ⟩
                         sym
                         (a ^^ (m +ℕ suc n)
                         ≡⟨ expEq a (m +ℕ suc n) (suc (m +ℕ n)) (addProp m n) ⟩
                         refl)

open Monoid{{...}} public

record MonoidHomomorphism (A : Set)(B : Set){{M : Monoid A}}{{M' : Monoid B}}(f : A → B) : Set where
  constructor mkMonoidHomomorphism
  field
    resp● : (a b : A) → (f (a ● b)) ≡ ((f a) ● (f b))
open MonoidHomomorphism{{...}} public
