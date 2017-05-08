module AlgebraStructures where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function

record Magma (A : Set) : Set where
  constructor mkMagma
  infixr 4 _●_
  field
    _●_ : A → A → A

record Semigroup (A : Set) : Set where
  constructor mkSemigroup
  infixr 4 _●_
  field
    _●_ : A → A → A
    assoc-semigroup : (x y z : A) → ((x ● y) ● z) ≡ (x ● (y ● z))

record Monoid (A : Set) : Set where
  constructor mkMonoid
  infixr 4 _●_
  field
    ε : A
    _●_ : A → A → A
    ε-unit₁ : (x : A) → (x ● ε) ≡ x
    ε-unit₂ : (x : A) → (ε ● x) ≡ x 
    assoc-Monoid : (x y z : A) → ((x ● y) ● z) ≡ (x ● (y ● z))
  semiA : Semigroup A
  semiA = mkSemigroup _●_ assoc-Monoid

record Group (A : Set) : Set where
  constructor mkGroup
  infixr 4 _●_
  field
    ε : A
    _●_ : A → A → A
    ε-unit₁ : (x : A) → (x ● ε) ≡ x
    ε-unit₂ : (x : A) → (ε ● x) ≡ x 
    assoc-Group : (x y z : A) → ((x ● y) ● z) ≡ (x ● (y ● z))
    inv : A → A
    inv-axiom₁ : (a : A) → (inv a ● a) ≡ ε
    inv-axiom₂ : (a : A) → (a ● (inv a)) ≡ ε
  commutator : (a b : A) → A
  commutator a b = (inv a) ● (inv b) ● a ● b
  mult : A → A → A
  mult x y = x ● y
  semiA : Semigroup A
  semiA = mkSemigroup _●_ assoc-Group
  
  monA : Monoid A
  monA = mkMonoid ε _●_ ε-unit₁ ε-unit₂ assoc-Group

  neut-Prop : (a : A) → (a ● ε) ≡ (ε ● a)
  neut-Prop a = trans (ε-unit₁ a) (sym (ε-unit₂ a))
  
  inv-Prop : (a : A) → (a ● (inv a)) ≡ ((inv a) ● a)
  inv-Prop a = trans (inv-axiom₂ a) (sym (inv-axiom₁ a))

  invElim₁ : (a b : A) → (a ● (inv b ● b)) ≡ a
  invElim₁ a b = begin ((a ● (inv b ● b))
                       ≡⟨ cong (mult a) (inv-axiom₁ b) ⟩
                       (a ● ε) ≡⟨ (ε-unit₁ a) ⟩ refl)

  invElim₂ : (a b : A) → ((inv b ● b) ● a) ≡ a
  invElim₂ a b = {!!}

  invElim : (a b c : A) → (a ● (inv b ● b) ● c) ≡ (a ● c)
  invElim a b c = begin {!!}
 
  
  jacketShirtLemma₁ : (a b : A) → (inv (a ● b) ● (a ● b)) ≡ ε
  jacketShirtLemma₁ a b = inv-axiom₁ (a ● b)
  
  jacketShirtLemma₂ : (a b : A) → (((inv b) ● (inv a) ● a) ● b) ≡ ε
  jacketShirtLemma₂ a b = begin (((inv b) ● (inv a) ● a) ● b) ≡⟨ (assoc-Group (inv b) (inv a ● a) b) ⟩
                          ((inv b) ● ((inv a ● a) ● b) ≡⟨ invElim (inv b) a b ⟩
                          inv-axiom₁ b)
  
  jacketShirt : (a b : A) → (inv (a ● b)) ≡ ((inv b) ● (inv a))
  jacketShirt a b = {!!}
open Group {{...}} public
  
record Abelian (A : Set) : Set where
  constructor mkAbelian
  field
    ε : A
    _●_ : A → A → A
    ε-unit : (x : A) → (x ● ε) ≡ x
    assoc-Monoid : (x y z : A) → ((x ● y) ● z) ≡ (x ● (y ● z))
    inv : A → A
    inv-axiom : (a : A) → ((inv a) ● a) ≡ ε
    commute : (a b : A) → (a ● b) ≡ (b ● a)

record Ring (A : Set) : Set where
  constructor mkRing
  infixr 5 _·_
  infixr 4 _+_
  field
      θ : A
      invPlus : A → A
      _+_ : A → A → A
      _·_ : A → A → A
      +-assoc : (a b c : A) → ((a + b) + c) ≡ (a + (b + c))
      +-commute : (a b : A) → (a + b) ≡ (b + a)
      +-inv : (a : A) → ((invPlus a) + a) ≡ θ
      +-θ : (a : A) → (a + θ) ≡ a
      θ-unit : (x : A) → (θ + x) ≡ x
      ·-distr-left : (a b c : A) → ((a + b) · c) ≡ ((a · c) + (b · c))
      ·-distr-right : (a b c : A) → (a · (b + c)) ≡ ((a · b) + (a · c))
      ·-assoc : (a b c : A) → ((a · b) · c) ≡ (a · (b · c))
  abA : Abelian A
  abA = mkAbelian θ _+_ +-θ +-assoc invPlus +-inv +-commute
  


record LeeRing (A : Set){{R : Ring A}} : Set where
  constructor mkLeeRing
  open Ring {{...}}
  field
    leeAxiom₁ : (a : A) → (a · a) ≡ θ
    leeAxiom₂ : (a b c : A) → (((a · b) · c) + (b · (a · c)) + (c · (a · b))) ≡ θ
  anticommute : (a b : A) → (a · b) ≡ ((invPlus b) · a)
  anticommute a b = begin ((a · b) ≡⟨ {!!} ⟩ {!!})

record BoolRing (A : Set){{R : Ring A}} : Set where
  constructor mkBoolRing
  open Ring {{...}}
  field
    imdepotency : (a : A) → (a · a) ≡ a

record RingWithOne (A : Set){{R : Ring A}} : Set where
  constructor mkAssocRingWithOne
  open Ring {{...}}
  field
    ε : A
    ·-unit₁ : (a : A) → (a · ε) ≡ a
    ·-unit₂ : (a : A) → (ε · a) ≡ a

record CommutativeRing (A : Set){{R : Ring A}} : Set where
  constructor mkCommutativeRing
  open Ring {{...}}
  field
    com-· : (a b : A) → (a · b) ≡ (b · a)

record ComRingWithOne (A : Set){{R : Ring A}}{{OA : RingWithOne A}}{{CA : CommutativeRing A}} : Set where
  constructor mkComRingWithOne

{- record DivisionRing (A : Set){{R : Ring A}}{{OA : RingWithOne A}} : Set where
  constructor mkDivisionRing
  open Ring {{...}}
  open RingWithOne {{...}}
  field
    invTimes : A → A
    inv-·₁ : (a : A) → (a · (invTimes a)) ≡ ε
    inv-·₂ : (a : A) → ((invTimes a) · a) ≡ a

record Field (A : Set){{R : Ring A}}{{OA : RingWithOne A}}{{DA : DivisionRing A}}{{CA : CommutativeRing A }} : Set where
  constructor mkField
-}

