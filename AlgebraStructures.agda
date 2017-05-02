module AlgebraStructures where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)

record Monoid (A : Set) : Set where
  constructor mkMonoid
  infixr 4 _●_
  field
    ε : A
    _●_ : A → A → A
    ε-unit₁ : (x : A) → (x ● ε) ≡ x
    ε-unit₂ : (x : A) → x ≡ (x ● ε)
    assoc-Monoid : (x y z : A) → ((x ● y) ● z) ≡ (x ● (y ● z))


