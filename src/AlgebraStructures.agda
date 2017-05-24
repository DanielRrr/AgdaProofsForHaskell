module AlgebraStructures where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
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
  
  _∶_ : (a b : A) → A
  a ∶ b = a ● inv b

  div : (a b : A) → A
  div a b = a ∶ b
  
  mult : A → A → A
  mult x y = x ● y

  semiA : Semigroup A
  semiA = mkSemigroup _●_ assoc-Group
  
  monA : Monoid A
  monA = mkMonoid ε _●_ ε-unit₁ ε-unit₂ assoc-Group

  mon-● : (a b c : A) → a ≡ b → (a ● c) ≡ (b ● c)
  mon-● a b c refl = refl

  mon-●₁ : (a b c : A) → a ≡ b → (c ● a) ≡ (c ● b)
  mon-●₁ a b c refl = refl

  neut-Prop : (a : A) → (a ● ε) ≡ (ε ● a)
  neut-Prop a = trans (ε-unit₁ a) (sym (ε-unit₂ a))
  
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
  jacketShirtLemma₂ a b = begin (((inv b) ● (inv a) ● a) ● b) ≡⟨ (assoc-Group (inv b) (inv a ● a) b) ⟩
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
                     ≡⟨ sym (assoc-Group a (inv a) b) ⟩
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
               ≡⟨ sym (assoc-Group a (_●_ (_●_ a (inv a)) (inv (a ● inv a))) (inv (a ● inv a))) ⟩
               ((a ● (a ● inv a) ● inv (a ● inv a)) ● inv (a ● inv a))
               ≡⟨ cong (_●_ (_●_ a (_●_ (_●_ a (inv a)) (inv (a ● inv a))))) (jacketShirt a (inv a)) ⟩
               ((a ● (a ● inv a) ● inv (a ● inv a)) ● inv (inv a) ● inv a)
               ≡⟨ assoc-Group a (_●_ (_●_ a (inv a)) (inv (a ● inv a))) (_●_ (inv (inv a)) (inv a)) ⟩
               (a ● ((a ● inv a) ● inv (a ● inv a)) ● inv (inv a) ● inv a) ≡⟨ refl ⟩
               (a ● ((a ● inv a) ● inv (a ● inv a)) ● (inv (inv a) ● inv a))
               ≡⟨ sym (assoc-Group a ((a ● inv a) ● inv (a ● inv a)) ((inv (inv a) ● inv a))) ⟩
               ((a ● (a ● inv a) ● inv (a ● inv a)) ● inv (inv a) ● inv a)
               ≡⟨ (cong (_●_ (_●_ a (_●_ (_●_ a (inv a)) (inv (a ● inv a))))) (sym (inv-Prop (inv a)))) ⟩
               ((a ● (a ● inv a) ● inv (a ● inv a)) ● inv a ● inv (inv a))
               ≡⟨ mon-● (a ● (a ● inv a) ● inv (a ● inv a)) a (inv a ● inv (inv a)) (invLemma100500 a (a ● inv a)) ⟩
               (a ● inv a ● inv (inv a)) ≡⟨ invLemma100501 a (inv (inv a)) ⟩ refl)
                 
  cancel₁ : (a b c : A) → ((a ● b) ≡ (a ● c)) → b ≡ c
  cancel₁ a b c f = begin
                b ≡⟨ (sym (ε-unit₂ b)) ⟩
                (ε ● b) ≡⟨ mon-● ε (inv a ● a) b (sym (inv-axiom₁ a)) ⟩
                ((inv a ● a) ● b) ≡⟨ (assoc-Group (inv a) a b) ⟩
                (inv a ● a ● b) ≡⟨ (cong (_●_ (inv a)) f) ⟩
                (inv a ● a ● c) ≡⟨ (sym (assoc-Group (inv a) a c)) ⟩
                (((inv a ● a) ● c) ≡⟨ (mon-● (inv a ● a) ε c (inv-axiom₁ a)) ⟩
                ε-unit₂ c)

  cancel₂ : (a b c : A) → ((a ● c) ≡ (b ● c)) → a ≡ b
  cancel₂ a b c f = begin
                    a
                    ≡⟨ sym (ε-unit₁ a) ⟩
                    a ● ε
                    ≡⟨ mon-●₁ ε (c ● inv c) a (sym (inv-axiom₂ c)) ⟩
                    a ● c ● inv c
                    ≡⟨ sym (assoc-Group a c (inv c)) ⟩
                    (a ● c) ● inv c
                    ≡⟨ mon-● (a ● c) (b ● c) (inv c) f ⟩
                    (b ● c) ● inv c
                    ≡⟨ assoc-Group b c (inv c) ⟩
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
                      (inv (a ● b) ● b ≡⟨ mon-● (inv (a ● b)) (inv b ● inv a) b (jacketShirt a b) ⟩ assoc-Group (inv b) (inv a) b)))) ⟩
                      ((inv b ● inv a ● b) ● a) ≡⟨ (assoc-Group (inv b) (inv a ● b) a) ⟩
                      inv b ● (inv a ● b) ● a
                      ≡⟨ mon-●₁ ((inv a ● b) ● a) (inv a ● b ● a) (inv b) (assoc-Group (inv a) b a) ⟩
                      refl))

  commmutatorTheorem : (a b : A) → ((commutator a b) ≡ ε) → (a ● b) ≡ (b ● a)
  commmutatorTheorem a b f = sym
                             (begin
                             (b ● a) ≡⟨ (mon-●₁ a (a ● commutator a b) b (sym ((a ● commutator a b) ≡⟨ (mon-●₁ (commutator a b) ε a f) ⟩ ε-unit₁ a))) ⟩
                             (b ● a ● commutator a b) ≡⟨ refl ⟩
                             (b ● a ● (inv a ● inv b ● a ● b))
                             ≡⟨ mon-●₁ (a ● (inv a ● inv b ● a ● b)) (inv b ● a ● b) b ((a ● inv a ● inv b ● a ● b) ≡⟨ sym (assoc-Group a (inv a) (inv b ● a ● b)) ⟩
                             ((a ● inv a) ● inv b ● a ● b) ≡⟨ (mon-● (a ● inv a) ε (inv b ● a ● b) (inv-axiom₂ a)) ⟩ ε-unit₂ (inv b ● a ● b)) ⟩
                             (b ● inv b ● a ● b) ≡⟨ (sym (assoc-Group b (inv b) (a ● b))) ⟩
                             ((b ● inv b) ● a ● b) ≡⟨ (mon-● (b ● inv b) ε (a ● b) (inv-axiom₂ b)) ⟩ ε-unit₂ (a ● b))
                       
                         
                     
open Group {{...}} public
  
record Abelian (A : Set){{GR : Group A}} : Set where
  constructor mkAbelian
  field
    commute : (a b : A) → (a ● b) ≡ (b ● a)
open Abelian {{...}} public

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
      +-inv₁ : (a : A) → ((invPlus a) + a) ≡ θ
      +-inv₂ : (a : A) → (a + invPlus a) ≡ θ
      +-θ : (a : A) → (a + θ) ≡ a
      θ-unit : (x : A) → (θ + x) ≡ x
      ·-distr-left : (a b c : A) → ((a + b) · c) ≡ ((a · c) + (b · c))
      ·-distr-right : (a b c : A) → (a · (b + c)) ≡ ((a · b) + (a · c))

  cong-+ : (a b c : A) → a ≡ b → (a + c) ≡ (b + c)
  cong-+ a b c refl = refl

  cong-· : (a b c : A) → a ≡ b → (a · c) ≡ (b · c)
  cong-· a b c refl = refl

  id₁ : (a b : A) → ((invPlus a) + (a + b)) ≡ b
  id₁ a b = begin
            (invPlus a + a + b)
            ≡⟨ sym (+-assoc (invPlus a) a b) ⟩
            ((invPlus a + a) + b) ≡⟨ cong-+ (invPlus a + a) θ b (+-inv₁ a) ⟩ θ-unit b

  id₂ : (a : A) → ((invPlus a) + a) ≡ (a + invPlus a)
  id₂ a = trans (+-inv₁ a) (sym (+-inv₂ a))

  [_,_,_] : (a b c : A) → A
  [_,_,_] a b c = (a · b · c) + invPlus (a · (b · c))
  
open Ring {{...}} public


  


record LeeRing (A : Set){{R : Ring A}} : Set where
  constructor mkLeeRing
  field
    leeAxiom₁ : (a : A) → (a · a) ≡ θ
    leeAxiom₂ : (a b c : A) → (((a · b) · c) + (b · (a · c)) + (c · (a · b))) ≡ θ
  anticommute : (a b : A) → (a · b) ≡ ((invPlus b) · a)
  anticommute a b = {!!}
  
record BoolRing (A : Set){{R : Ring A}} : Set where
  constructor mkBoolRing
  field
    imdepotency : (a : A) → (a · a) ≡ a
  

record RingWithOne (A : Set){{R : Ring A}} : Set where
  constructor mkAssocRingWithOne
  field
    ε : A
    ·-unit₁ : (a : A) → (a · ε) ≡ a
    ·-unit₂ : (a : A) → (ε · a) ≡ a
  

record CommutativeRing (A : Set){{R : Ring A}} : Set where
  constructor mkCommutativeRing
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

