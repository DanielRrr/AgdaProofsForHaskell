module AlgebraStructures where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)

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
    ε-unit₂ : (x : A) → x ≡ (x ● ε)
    assoc-Monoid : (x y z : A) → ((x ● y) ● z) ≡ (x ● (y ● z))

record Group (A : Set){{AG : Monoid A}} : Set where
  constructor mkGroup
  open Monoid {{...}}
  field
    inv : A → A
    inv-axiom₁ : (a : A) → ((inv a) ● a) ≡ ε
    inv-axiom₁ : (a : A) → (a ● (inv a)) ≡ ε

record Abelian (A : Set){{AM : Monoid A}}{{AG : Group A}} : Set where
  constructor mkAbelian
  open Monoid {{...}}
  open Group {{...}}
  field
    commute : (a b : A) → (a ● b) ≡ (b ● a)

record AbelianMonoid (A : Set){{AM : Monoid A}} : Set where
 constructor mkAbelianMonoid
 open Monoid {{...}}
 field
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
      +-assoc : (a b c : A) → (a + (b + c)) ≡ ((a + b) + c)
      +-commute : (a b : A) → (a + b) ≡ (b + a)
      +-inv : (a : A) → (a + (invPlus a)) ≡ θ
      +-θ : (a : A) → (a + θ) ≡ a
      ·-distr-left : (a b c : A) → ((a + b) · c) ≡ ((a · c) + (b · c))
      ·-distr-right : (a b c : A) → (a · (b + c)) ≡ ((a · b) + (a · c))
      ·-assoc : (a b c : A) → (a · (b · c)) ≡ ((a · b) · c)
      associator : A → A → A → A

record LeeRing (A : Set){{R : Ring A}} : Set where
  constructor mkLeeRing
  open Ring {{...}}
  field
    leeAxiom₁ : (a : A) → (a · a) ≡ θ
    leeAxiom₂ : (a b c : A) → (((a · b) · c) + (b · (a · c)) + (c · (a · b))) ≡ θ

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

record DivisionRing (A : Set){{R : Ring A}}{{OA : RingWithOne A}} : Set where
  constructor mkDivisionRing
  open Ring {{...}}
  open RingWithOne {{...}}
  field
    invTimes : A → A
    inv-·₁ : (a : A) → (a · (invTimes a)) ≡ ε
    inv-·₂ : (a : A) → ((invTimes a) · a) ≡ a

record Field (A : Set){{R : Ring A}}{{OA : RingWithOne A}}{{DA : DivisionRing A}}{{CA : CommutativeRing A }} : Set where
  constructor mkField


