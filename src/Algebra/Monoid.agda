module Monoid where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function
open import Data.Product
open import Data.Nat
import Data.Nat.Properties

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

  plusZero : (n : ℕ) → n + zero ≡ n
  plusZero zero = refl
  plusZero (suc n) = begin
                   (suc n + zero
                   ≡⟨ refl ⟩
                   suc (n + zero)
                   ≡⟨ cong suc (plusZero n) ⟩
                   refl)

  expEq : (a : A) → (m n : ℕ) → (m ≡ n) → (a ^^ m) ≡ (a ^^ n)
  expEq a m n refl = refl

  postulate addProp : (m n : ℕ) → (m + suc n) ≡ (suc (m + n))
  

  expProp1 : (a : A) → (m n : ℕ) → ((a ^^ m) ● (a ^^ n)) ≡ (a ^^ (m + n))
  expProp1 a m zero = begin
                      (a ^^ m) ● (a ^^ zero)
                      ≡⟨ mon-●₁ (a ^^ zero) ε (a ^^ m) refl ⟩
                      (a ^^ m) ● ε
                      ≡⟨ ε-unit₁ (a ^^ m) ⟩
                      a ^^ m
                      ≡⟨ ^^prop a m (m + zero) (sym (plusZero m)) ⟩
                      refl
  expProp1 a m (suc n) = begin
                         (a ^^ m) ● (a ^^ (suc n)) 
                         ≡⟨ refl ⟩
                         (a ^^ m) ● (a ^^ n) ● a
                         ≡⟨ sym (assoc (a ^^ m) (a ^^ n) a) ⟩
                         ((a ^^ m) ● (a ^^ n)) ● a
                         ≡⟨ mon-● ((a ^^ m) ● (a ^^ n)) (a ^^ (m + n)) a (expProp1 a m n) ⟩
                         sym
                         (a ^^ (m + suc n)
                         ≡⟨ expEq a (m + suc n) (suc (m + n)) (addProp m n) ⟩
                         refl)

  expLemma : (n : ℕ) → ε ^^ n ≡ ε
  expLemma zero = refl
  expLemma (suc n) = begin
                     (ε ^^ suc n
                     ≡⟨ refl ⟩
                     ε ^^ n ● ε
                     ≡⟨ mon-● (ε ^^ n) ε ε (expLemma n) ⟩
                     ε-unit₁ ε)

  expLemma₁ : (a : A) → (m : ℕ) → ((a ^^ m) ● a) ≡ (a ● (a ^^ m))
  expLemma₁ a zero = begin
                     (a ^^ zero ● a
                      ≡⟨ refl ⟩
                      ε ● a
                      ≡⟨ ε-unit₂ a ⟩
                      sym
                      (a ● a ^^ zero
                      ≡⟨ mon-●₁ (a ^^ zero) ε a refl ⟩
                      ε-unit₁ a))
  expLemma₁ a (suc m) = begin
                      a ^^ suc m ● a
                      ≡⟨ refl ⟩
                      (a ^^ m ● a) ● a
                      ≡⟨ mon-● (a ^^ m ● a) (a ● (a ^^ m)) a (expLemma₁ a m) ⟩
                      (a ● a ^^ m) ● a
                      ≡⟨ assoc a (a ^^ m) a ⟩
                      a ● a ^^ m ● a
                      ≡⟨ mon-●₁ (a ^^ m ● a) (a ^^ suc m) a (sym refl) ⟩
                      refl

  expLemma₂ : (a b : A) → (m : ℕ) → (a ≡ b) → a ^^ m ≡ b ^^ m
  expLemma₂ a b m refl = refl

  expLemma₃ : (a : A) → a ^^ 1 ≡ a
  expLemma₃ a = begin
                a ^^ suc zero
                ≡⟨ refl ⟩
                a ^^ zero ● a
                ≡⟨ mon-● (a ^^ zero) ε a refl ⟩
                ε-unit₂ a

        
  expProp2 : (a : A) → (m n : ℕ) → ((a ^^ m) ^^ n) ≡ (a ^^ (m * n))
  expProp2 a m zero = begin
                      (a ^^ m) ^^ zero
                      ≡⟨ refl ⟩
                      ε
                      ≡⟨ refl ⟩
                      sym
                      (a ^^ (m * zero)
                      ≡⟨ ^^prop a (m * zero) zero (Data.Nat.Properties.*-comm m zero) ⟩
                      refl)
  expProp2 a m (suc n) = begin
                       (a ^^ m) ^^ suc n
                       ≡⟨ ^^prop (a ^^ m) (suc n) (1 + n) refl ⟩
                       (a ^^ m) ^^ (1 + n)
                       ≡⟨ sym (expProp1 (a ^^ m) 1 n) ⟩
                       (a ^^ m) ^^ 1 ● (a ^^ m) ^^ n
                       ≡⟨ mon-●₁ ((a ^^ m) ^^ n) (a ^^ (m * n)) ((a ^^ m) ^^ 1) (expProp2 a m n) ⟩
                       (a ^^ m) ^^ 1 ● a ^^ (m * n)
                       ≡⟨ mon-● ((a ^^ m) ^^ 1) (a ^^ m) ( a ^^ (m * n)) (expLemma₃ (a ^^ m)) ⟩
                       a ^^ m ● a ^^ (m * n)
                       ≡⟨ mon-●₁ (a ^^ (m * n)) (a ^^ (n * m)) (a ^^ m) (^^prop a (m * n) (n * m) (Data.Nat.Properties.*-comm m n)) ⟩
                       a ^^ m ● a ^^ (n * m)
                       ≡⟨ expProp1 a m (n * m) ⟩
                       a ^^ (m + n * m)
                       ≡⟨ ^^prop a (m + n * m) (suc n * m) (sym refl) ⟩
                       a ^^ (suc n * m)
                       ≡⟨ ^^prop a (suc n * m) (m * suc n) (Data.Nat.Properties.*-comm (suc n) m) ⟩
                       refl                                                                                                                                    
                                                                                       
open Monoid {{...}} public

record MonoidHomomorphism (A : Set)(B : Set){{M : Monoid A}}{{M' : Monoid B}}(f : A → B) : Set where
  constructor mkMonoidHomomorphism
  field
    resp● : (a b : A) → (f (a ● b)) ≡ ((f a) ● (f b))
open MonoidHomomorphism{{...}} public

∘-Homo : (A : Set)(B : Set)(C : Set)(f : A → B)(g : B → C)
             {{M₁ : Monoid A}}{{M₂ : Monoid B}}{{M₃ : Monoid C}}{{MH₁ : MonoidHomomorphism A B f}}{{MH₂ : MonoidHomomorphism B C g}}
             → MonoidHomomorphism A C (g ∘ f)
∘-Homo A B C f g = mkMonoidHomomorphism λ a → λ b →
                                              begin
                                              (g ∘ f) (a ● b)
                                              ≡⟨ refl ⟩
                                              g (f (a ● b))
                                              ≡⟨ cong g (resp● a b) ⟩
                                              g ((f a) ● (f b))
                                              ≡⟨ resp● (f a) (f b) ⟩
                                              refl


pairProd : ∀ {A B : Set} → (a b : A × B) → (proj₁ a ≡ proj₁ b) → (proj₂ a ≡ proj₂ b) → (a ≡ b)
pairProd a b refl refl = refl

prodMonoid : (A : Set)(B : Set){{M₁ : Monoid A}}{{M₂ : Monoid B}} → Monoid (A × B)
prodMonoid A B = mkMonoid (λ x → λ y → ( proj₁ x ● proj₁ y) , proj₂ x ● proj₂ y)
                           (ε , ε)
                           (λ x y z →
                           pairProd
                           ( ((proj₁ x ● proj₁ y) ● proj₁ z) , (proj₂ x ● proj₂ y) ● proj₂ z)
                           ((proj₁ x ● proj₁ y ● proj₁ z) , ((proj₂ x ● proj₂ y ● proj₂ z)))
                           (assoc (proj₁ x) (proj₁ y) (proj₁ z))
                           (assoc (proj₂ x) (proj₂ y) (proj₂ z)))
                           (λ x →
                           begin
                           (proj₁ x ● ε) , (proj₂ x ● ε)
                           ≡⟨ pairProd ((proj₁ x ● ε) , (proj₂ x ● ε)) x (ε-unit₁ (proj₁ x)) (ε-unit₁ (proj₂ x)) ⟩
                           refl)
                           (λ x →
                           begin
                           ((ε ● proj₁ x) , (ε ● proj₂ x)
                           ≡⟨ pairProd ((ε ● proj₁ x) , (ε ● proj₂ x)) x (ε-unit₂ (proj₁ x)) (ε-unit₂ (proj₂ x)) ⟩
                           refl))

record Monomorphism (A : Set)(B : Set)(f : A → B){{M₁ : Monoid A}}{{M₂ : Monoid B}}{{F : MonoidHomomorphism A B f}} : Set where
  constructor mkMonomorphism
  field
    monic : (a b : A) → (f a ≡ f b) → a ≡ b
open Monomorphism {{...}} public

record MonoidIso (A : Set)(B : Set)(f : A → B){{M₁ : Monoid A}}{{M₂ : Monoid B}}{{F : MonoidHomomorphism A B f}} : Set where
  constructor mkMonoidIso
  field
    iso : (a : A) → (b : B) → Σ (B → A) (λ g → (((f ∘ g) $ b) ≡ b) × ((g ∘ f) $ a) ≡ a)
open MonoidIso {{...}} public
