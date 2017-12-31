{-# OPTIONS --allow-unsolved-metas #-}

module Group where

open import Monoid
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function
open import Data.Product
open import Data.List
open import Data.Fin.Subset
open import Data.Nat
open import Data.Vec as V
open import Data.Integer

record Group (A : Set){{Mo : Monoid A}} : Set where
  constructor mkGroup
  field
    inv : A → A
    inv-axiom₁ : (a : A) → (inv a ● a) ≡ ε
    inv-axiom₂ : (a : A) → (a ● (inv a)) ≡ ε

  commutator : (a b : A) → A
  commutator a b = (inv a) ● (inv b) ● a ● b

  _∶_ : (a b : A) → A
  a ∶ b = a ● inv b

  div : (a b : A) → A
  div a b = a ∶ b

  mult : A → A → A
  mult x y = x ● y


  inv-Prop : (a : A) → (a ● (inv a)) ≡ ((inv a) ● a)
  inv-Prop a = trans (inv-axiom₂ a) (sym (inv-axiom₁ a))

  invElim₁ : (a b : A) → (a ● (inv b ● b)) ≡ a
  invElim₁ a b = begin ((a ● (inv b ● b))
                       ≡⟨ cong (mult a) (inv-axiom₁ b) ⟩
                       (a ● ε) ≡⟨ (ε-unit₁ a) ⟩ refl)

  invElim₂ : (a b : A) → ((inv b ● b) ● a) ≡ a
  invElim₂ a b = begin
                 ((inv b ● b) ● a)
                 ≡⟨ mon-● (_●_ (inv b) b) ε a (inv-axiom₁ b) ⟩
                 ε-unit₂ a

  invElim : (a b c : A) → (a ● (inv b ● b) ● c) ≡ (a ● c)
  invElim a b c = begin (a ● (inv b ● b) ● c) ≡⟨ (cong (mult a) (invElim₂ c b)) ⟩ refl


  jacketShirtLemma₁ : (a b : A) → (inv (a ● b) ● (a ● b)) ≡ ε
  jacketShirtLemma₁ a b = inv-axiom₁ (a ● b)

  jS : (a b : A) → ((a ● b) ● inv (a ● b)) ≡ ε
  jS a b = inv-axiom₂ (a ● b)

  jacketShirtLemma₂ : (a b : A) → (((inv b) ● (inv a) ● a) ● b) ≡ ε
  jacketShirtLemma₂ a b = begin (((inv b) ● (inv a) ● a) ● b) ≡⟨ (assoc (inv b) (inv a ● a) b) ⟩
                          ((inv b) ● ((inv a ● a) ● b) ≡⟨ invElim (inv b) a b ⟩
                          inv-axiom₁ b)

  invLemmaforJS : (a : A) → inv a ≡ (inv a ● inv a ● a)
  invLemmaforJS a = sym $ (inv a ● inv a ● a) ≡⟨ invElim₁ (inv a) a ⟩ refl

  invP : (a : A) → ((a ● inv a) ● inv a) ≡ inv a
  invP a = begin
           ((a ● inv a) ● inv a
           ≡⟨ mon-● (a ● inv a) ε (inv a) (inv-axiom₂ a) ⟩
           ε ● inv a ≡⟨ ε-unit₂ (inv a) ⟩ refl)

  divInv : (a : A) → inv a ≡ ((a ∶ a) ∶ a)
  divInv a = sym $ begin
             (((a ∶ a) ∶ a) ≡⟨ refl ⟩
             _●_ (_●_ a (inv a)) (inv a)
             ≡⟨ refl ⟩
             ((a ● inv a) ● inv a)
             ≡⟨ invP a ⟩
             refl)

  unit-prop : inv ε ≡ ε
  unit-prop = sym $ begin
              ε ≡⟨ sym (inv-axiom₁ ε) ⟩
              sym (begin
              (inv ε) ≡⟨ sym (ε-unit₁ (inv ε)) ⟩ refl)

  divE : (a : A) → (a ∶ a) ≡ ε
  divE a = begin
           ((a ● inv a) ≡⟨ inv-axiom₂ a ⟩ refl)

  divE₁ : (a : A) → a ∶ (a ∶ a) ≡ a
  divE₁ a = begin
            (_●_ a (inv (a ∶ a))
            ≡⟨ cong (mult a) (cong inv (divE a)) ⟩
            (a ● (inv ε)) ≡⟨ cong (_●_ a) unit-prop ⟩
            (_●_ a ε) ≡⟨ (ε-unit₁ a) ⟩ refl)

  invLemma : (a : A) → (inv (inv a) ● (inv a)) ≡ ε
  invLemma a = inv-axiom₁ (inv a)

  invLemma100500 : (a b : A) → (a ● b ● inv b) ≡ a
  invLemma100500 a b = begin
                     ((a ● b ● inv b) ≡⟨ cong (_●_ a) (inv-axiom₂ b) ⟩
                     ε-unit₁ a)

  invLemma100501 : (a b : A) → (a ● inv a ● b) ≡ b
  invLemma100501 a b =
                     (a ● inv a ● b)
                     ≡⟨ sym (assoc a (inv a) b) ⟩
                     ((a ● inv a) ● b) ≡⟨ (mon-● (a ● inv a) ε b (inv-axiom₂ a)) ⟩ (ε-unit₂ b)

  invLemma100502 : (a b : A) → (inv a ● (a ● b) ● inv (a ● b)) ≡ inv a
  invLemma100502 a b = begin
                       (inv a ● (a ● b) ● inv (a ● b))
                       ≡⟨ (cong (_●_ (inv a)) (inv-axiom₂ (a ● b))) ⟩ ε-unit₁ (inv a)


  postulate
    bracketLemma : (a b c d e : A) → (a ● b ● (c ● d) ● e) ≡ (((a ● b ● c) ● d) ● e)

  jacketShirt : (a b : A) → (inv (a ● b)) ≡ ((inv b) ● (inv a))
  jacketShirt a b = sym $ begin
                          ((inv b) ● (inv a))
                          ≡⟨ (mon-●₁ (inv a) (inv a ● (a ● b) ● inv (a ● b)) (inv b) (sym (invLemma100502 a b))) ⟩
                          inv b ● inv a ● (a ● b) ● inv (a ● b) ≡⟨ bracketLemma (inv b) (inv a) a b (inv (a ● b)) ⟩
                          (((inv b) ● (inv a) ● a) ● b) ● inv (a ● b)
                          ≡⟨ mon-● ((((inv b) ● (inv a) ● a) ● b)) ε (inv (a ● b)) (jacketShirtLemma₂ a b) ⟩
                          ε-unit₂ (inv (a ● b))


  invTheorem : (a : A) → inv (inv a) ≡ a
  invTheorem a = sym $
               begin a ≡⟨ sym (divE₁ a) ⟩
               (a ∶ (a ∶ a)
               ≡⟨ refl ⟩
               (_●_ a (inv (a ∶ a)))
               ≡⟨ cong (_●_ a) (divInv (a ∶ a)) ⟩
               _●_ a (_●_ (_●_ (_●_ a (inv a)) (inv (_●_ a (inv a)))) (inv (_●_ a (inv a))))
               ≡⟨ sym (assoc a (_●_ (_●_ a (inv a)) (inv (a ● inv a))) (inv (a ● inv a))) ⟩
               ((a ● (a ● inv a) ● inv (a ● inv a)) ● inv (a ● inv a))
               ≡⟨ cong (_●_ (_●_ a (_●_ (_●_ a (inv a)) (inv (a ● inv a))))) (jacketShirt a (inv a)) ⟩
               ((a ● (a ● inv a) ● inv (a ● inv a)) ● inv (inv a) ● inv a)
               ≡⟨ assoc a (_●_ (_●_ a (inv a)) (inv (a ● inv a))) (_●_ (inv (inv a)) (inv a)) ⟩
               (a ● ((a ● inv a) ● inv (a ● inv a)) ● inv (inv a) ● inv a) ≡⟨ refl ⟩
               (a ● ((a ● inv a) ● inv (a ● inv a)) ● (inv (inv a) ● inv a))
               ≡⟨ sym (assoc a ((a ● inv a) ● inv (a ● inv a)) ((inv (inv a) ● inv a))) ⟩
               ((a ● (a ● inv a) ● inv (a ● inv a)) ● inv (inv a) ● inv a)
               ≡⟨ (cong (_●_ (_●_ a (_●_ (_●_ a (inv a)) (inv (a ● inv a))))) (sym (inv-Prop (inv a)))) ⟩
               ((a ● (a ● inv a) ● inv (a ● inv a)) ● inv a ● inv (inv a))
               ≡⟨ mon-● (a ● (a ● inv a) ● inv (a ● inv a)) a (inv a ● inv (inv a)) (invLemma100500 a (a ● inv a)) ⟩
               (a ● inv a ● inv (inv a)) ≡⟨ invLemma100501 a (inv (inv a)) ⟩ refl)


  cancel₁ : (a b c : A) → ((a ● b) ≡ (a ● c)) → b ≡ c
  cancel₁ a b c f = begin
                b ≡⟨ (sym (ε-unit₂ b)) ⟩
                (ε ● b) ≡⟨ mon-● ε (inv a ● a) b (sym (inv-axiom₁ a)) ⟩
                ((inv a ● a) ● b) ≡⟨ (assoc (inv a) a b) ⟩
                (inv a ● a ● b) ≡⟨ (cong (_●_ (inv a)) f) ⟩
                (inv a ● a ● c) ≡⟨ (sym (assoc (inv a) a c)) ⟩
                (((inv a ● a) ● c) ≡⟨ (mon-● (inv a ● a) ε c (inv-axiom₁ a)) ⟩
                ε-unit₂ c)

  cancel₂ : (a b c : A) → ((a ● c) ≡ (b ● c)) → a ≡ b
  cancel₂ a b c f = begin
                    a
                    ≡⟨ sym (ε-unit₁ a) ⟩
                    a ● ε
                    ≡⟨ mon-●₁ ε (c ● inv c) a (sym (inv-axiom₂ c)) ⟩
                    a ● c ● inv c
                    ≡⟨ sym (assoc a c (inv c)) ⟩
                    (a ● c) ● inv c
                    ≡⟨ mon-● (a ● c) (b ● c) (inv c) f ⟩
                    (b ● c) ● inv c
                    ≡⟨ assoc b c (inv c) ⟩
                    b ● c ● inv c
                    ≡⟨ mon-●₁ (c ● inv c) ε b (inv-axiom₂ c) ⟩
                    ε-unit₁ b

  commutatorLemma : (a b : A) → inv (commutator a b) ≡ (commutator b a)
  commutatorLemma a b = begin
                      ((inv (inv a ● inv b ● a ● b))
                      ≡⟨ jacketShirt (inv a) (inv b ● a ● b) ⟩
                      (inv (inv b ● a ● b) ● inv (inv a))
                      ≡⟨ (cong (_●_ (inv (inv b ● a ● b))) (invTheorem a)) ⟩
                      ((inv (inv b ● a ● b) ● a) ≡⟨ (mon-● (inv (inv b ● a ● b)) (inv b ● inv a ● b) a
                      (begin
                      ((inv (inv b ● a ● b)) ≡⟨ (jacketShirt (inv b) (a ● b)) ⟩
                      (inv (a ● b) ● inv (inv b)) ≡⟨ (cong (_●_ (inv (a ● b))) (invTheorem b)) ⟩
                      (inv (a ● b) ● b ≡⟨ mon-● (inv (a ● b)) (inv b ● inv a) b (jacketShirt a b) ⟩ assoc (inv b) (inv a) b)))) ⟩
                      ((inv b ● inv a ● b) ● a) ≡⟨ (assoc (inv b) (inv a ● b) a) ⟩
                      inv b ● (inv a ● b) ● a
                      ≡⟨ mon-●₁ ((inv a ● b) ● a) (inv a ● b ● a) (inv b) (assoc (inv a) b a) ⟩
                      refl))

  commmutatorTheorem : (a b : A) → ((commutator a b) ≡ ε) → (a ● b) ≡ (b ● a)
  commmutatorTheorem a b f = sym
                             (begin
                             (b ● a) ≡⟨ (mon-●₁ a (a ● commutator a b) b (sym ((a ● commutator a b) ≡⟨ (mon-●₁ (commutator a b) ε a f) ⟩ ε-unit₁ a))) ⟩
                             (b ● a ● commutator a b) ≡⟨ refl ⟩
                             (b ● a ● (inv a ● inv b ● a ● b))
                             ≡⟨ mon-●₁ (a ● (inv a ● inv b ● a ● b)) (inv b ● a ● b) b ((a ● inv a ● inv b ● a ● b) ≡⟨ sym (assoc a (inv a) (inv b ● a ● b)) ⟩
                             ((a ● inv a) ● inv b ● a ● b) ≡⟨ (mon-● (a ● inv a) ε (inv b ● a ● b) (inv-axiom₂ a)) ⟩ ε-unit₂ (inv b ● a ● b)) ⟩
                             (b ● inv b ● a ● b) ≡⟨ (sym (assoc b (inv b) (a ● b))) ⟩
                             ((b ● inv b) ● a ● b) ≡⟨ (mon-● (b ● inv b) ε (a ● b) (inv-axiom₂ b)) ⟩ ε-unit₂ (a ● b))

  leftCoset : (a : A) → List A → List A
  leftCoset a [] = []
  leftCoset a (x ∷ xs) = (a ● x) ∷ leftCoset a xs

  rightCoset : List A → (a : A) → List A
  rightCoset [] a = []
  rightCoset (x ∷ xs) a = (x ● a) ∷ rightCoset xs a

  eq-leftCoset : (a b : A) → (xs : List A) → (a ≡ b) → leftCoset a xs ≡ leftCoset b xs
  eq-leftCoset a b xs refl = refl

  eq-rightCoset :  (a b : A) → (xs : List A) → (a ≡ b) → rightCoset xs a ≡ rightCoset xs b
  eq-rightCoset a b xs refl = refl

open Group {{...}} public

record Abelian (A : Set){{Mon : Monoid A}}{{GR : Group A}} : Set where
  constructor mkAbelian
  field
    commute : (a b : A) → (a ● b) ≡ (b ● a)

  listProp : (x y : A) → (xs ys : List A) → (x ≡ y) → (xs ≡ ys) → (x ∷ xs) ≡ (y ∷ ys)
  listProp x y xs ys refl refl = refl

  CosetEq : (a : A) → (xs : List A) → leftCoset a xs ≡ rightCoset xs a
  CosetEq a [] = begin leftCoset a []
                       ≡⟨ refl ⟩
                       []
                       ≡⟨ refl ⟩
                       sym
                       (rightCoset [] a
                       ≡⟨ refl ⟩
                       []
                       ≡⟨ refl ⟩
                       refl)
  CosetEq a (x ∷ xs) = begin
                       leftCoset a (x ∷ xs)
                       ≡⟨ refl ⟩
                       (a ● x) ∷ leftCoset a xs
                       ≡⟨ listProp (a ● x) (x ● a) (leftCoset a xs) (rightCoset xs a) (commute a x) (CosetEq a xs) ⟩
                       refl
open Abelian {{...}} public


record GroupHomomorphism (A : Set)(B : Set){{M : Monoid A}}{{G : Group A}}{{M' : Monoid B}}{{G' : Group B}}(f : A → B){{MH : MonoidHomomorphism A B f}} : Set where
  constructor mkGroupHomomorphism

  resp-ε : f ε ≡ ε
  resp-ε = sym $ begin
           (ε
           ≡⟨ sym (inv-axiom₁ (f ε)) ⟩
           inv (f ε) ● f ε
           ≡⟨ mon-●₁ (f ε) (f (ε ● ε)) (inv (f ε)) (cong f (sym (ε-unit₁ ε))) ⟩
           (inv (f ε) ● f (ε ● ε))
           ≡⟨ mon-●₁ (f (ε ● ε)) ((f ε) ● (f ε)) (inv (f ε)) (resp● ε ε) ⟩
           inv (f ε) ● f ε ● f ε
           ≡⟨ sym (assoc (inv (f ε)) (f ε) (f ε)) ⟩
           ((inv (f ε) ● f ε) ● f ε)
           ≡⟨ mon-● (inv (f ε) ● f ε) ε (f ε) (inv-axiom₁ (f ε)) ⟩
           ε-unit₂ (f ε))

  resp-inv : (a : A) → f (inv a) ≡ inv (f a)  
  resp-inv a = begin
               f (inv a)
               ≡⟨ sym (ε-unit₁ (f (inv a))) ⟩
               f (inv a) ● ε
               ≡⟨ mon-●₁ ε (f a ● inv (f a)) (f (inv a)) (sym (inv-axiom₂ (f a))) ⟩
               f (inv a) ● f a ● inv (f a)
               ≡⟨ sym (assoc (f (inv a)) (f a) (inv (f a))) ⟩
               (f (inv a) ● f a) ● inv (f a)
               ≡⟨ mon-● (f (inv a) ● f a) (f (inv a ● a)) ( inv (f a)) (sym (resp● (inv a) a)) ⟩
               f (inv a ● a) ● inv (f a)
               ≡⟨ mon-● ( f (inv a ● a)) (f ε) (inv (f a)) (cong f (inv-axiom₁ a)) ⟩
               f ε ● inv (f a)
               ≡⟨ mon-● (f ε) ε (inv (f a)) resp-ε ⟩
               ε-unit₂ (inv (f a))
open GroupHomomorphism{{...}} public

data Image (A : Set)(B : Set){{M : Monoid A}}{{G : Group A}}{{M' : Monoid B}}{{G' : Group B}}(f : A → B){{GH : MonoidHomomorphism A B f}}{{GH : GroupHomomorphism A B f}} : Set where
  image : Σ B (λ y → (Σ A (λ x → f x ≡ y))) → Image A B f

data Ker (A : Set)(B : Set){{M : Monoid A}}{{G : Group A}}{{M' : Monoid B}}{{G' : Group B}}(f : A → B){{GH : MonoidHomomorphism A B f}}{{GH : GroupHomomorphism A B f}} : Set where
  kernel : Σ A (λ x → f x ≡ ε) → Ker A B f

