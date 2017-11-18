module AlgebraStructures where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function

record Magma (A : Set) : Set where
  constructor mkMagma
  infixr 4 _●_
  field
    _●_ : A → A → A
open Magma{{...}} public

record Semigroup (A : Set){{M : Magma A}} : Set where
  constructor mkSemigroup
  field
    assoc : (x y z : A) → ((x ● y) ● z) ≡ (x ● (y ● z))

  cancellation : (a b : A) → ((x : A) → ((x ● x ● x) ≡ x)) → (a ● b) ≡ (b ● a)
  cancellation a b f = {!!}
open Semigroup{{...}} public

record Monoid (A : Set){{M : Magma A}}{{S : Semigroup A}} : Set where
  constructor mkMonoid
  field
    ε : A
    ε-unit₁ : (x : A) → (x ● ε) ≡ x
    ε-unit₂ : (x : A) → (ε ● x) ≡ x

  neut-Prop : (a : A) → (a ● ε) ≡ (ε ● a)
  neut-Prop a = trans (ε-unit₁ a) (sym (ε-unit₂ a))
  
open Monoid{{...}} public



record Group (A : Set){{M : Magma A}}{{S : Semigroup A}}{{Mo : Monoid A}} : Set where
  constructor mkGroup
  field
    inv : A → A
    inv-axiom₁ : (a : A) → (inv a ● a) ≡ ε
    inv-axiom₂ : (a : A) → (a ● (inv a)) ≡ ε

  mon-● : (a b c : A) → a ≡ b → (a ● c) ≡ (b ● c)
  mon-● a b c refl = refl

  mon-●₁ : (a b c : A) → a ≡ b → (c ● a) ≡ (c ● b)
  mon-●₁ a b c refl = refl

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
                       

  fact : (a b : A) → ((x : A) → (x ● x) ≡ ε) → (a ● b) ≡ (b ● a)
  fact a b f = {!!}
                     
open Group {{...}} public
  
record Abelian (A : Set){{M : Magma A}}{{S : Semigroup A}}{{Mon : Monoid A}}{{GR : Group A}} : Set where
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

  cong-+₁ : (a b c : A) → a ≡ b → (c + a) ≡ (c + b)
  cong-+₁ a b c refl = refl

  cong-·₁ : (a b c : A) → a ≡ b → (a · c) ≡ (b · c)
  cong-·₁ a b c refl = refl

  cong-·₂ : (a b c : A) → a ≡ b → (c · a) ≡ (c · b)
  cong-·₂ a b c refl = refl

  id₁ : (a b : A) → ((invPlus a) + (a + b)) ≡ b
  id₁ a b = begin
            (invPlus a + a + b)
            ≡⟨ sym (+-assoc (invPlus a) a b) ⟩
            ((invPlus a + a) + b) ≡⟨ cong-+ (invPlus a + a) θ b (+-inv₁ a) ⟩ θ-unit b

  id₂ : (a : A) → ((invPlus a) + a) ≡ (a + invPlus a)
  id₂ a = trans (+-inv₁ a) (sym (+-inv₂ a))

  zeroLemma₁ : (a b : A) → (a · b) ≡ ((a · b) + (a · θ))
  zeroLemma₁ a b = begin
                   (a · b) ≡⟨ (cong-·₂ b (b + θ) a (sym (+-θ b))) ⟩
                   a · (b + θ) ≡⟨ ·-distr-right a b θ ⟩ refl

  zeroLemma₂ : (a b : A) → (b · a) ≡ ((b · a) + (θ · a))
  zeroLemma₂ a b = begin
                   ((b · a) ≡⟨ (cong-·₁ b (b + θ) a (sym (+-θ b))) ⟩
                   ((b + θ) · a) ≡⟨ (·-distr-left b θ a) ⟩ refl)

  distrLaw₁ : (a b c d : A) → ((a + b) · (c + d)) ≡ ((a · c) + (a · d) + (b · c) + (b · d))
  distrLaw₁ a b c d =
                ((a + b) · (c + d))
                ≡⟨ ·-distr-right (a + b) c d ⟩
                (a + b) · c + (a + b) · d
                ≡⟨ cong-+ ((a + b) · c) (a · c + b · c) ((a + b) · d) (·-distr-left a b c) ⟩
                (a · c + b · c) + (a + b) · d
                ≡⟨ +-commute (a · c + b · c) ((a + b) · d) ⟩
                (a + b) · d + a · c + b · c
                ≡⟨ cong-+ ((a + b) · d) (a · d + b · d) (a · c + b · c) (·-distr-left a b d) ⟩
                (a · d + b · d) + a · c + b · c
                ≡⟨ +-commute (a · d + b · d) (a · c + b · c) ⟩
                (a · c + b · c) + a · d + b · d
                ≡⟨ +-assoc (a · c) (b · c) (a · d + b · d) ⟩
                a · c + b · c + a · d + b · d
                ≡⟨ +-commute (a · c) (b · c + a · d + b · d) ⟩
                (b · c + a · d + b · d) + a · c
                ≡⟨ cong-+ (b · c + a · d + b · d) (a · d + b · c + b · d) (a · c) (b · c + a · d + b · d
                ≡⟨ sym (+-assoc (b · c) (a · d) ( b · d)) ⟩ ((b · c + a · d) + b · d)
                ≡⟨ cong-+ (b · c + a · d) (a · d + b · c) (b · d) (+-commute (b · c) (a · d)) ⟩
                +-assoc (a · d) (b · c) (b · d)) ⟩
                (a · d + b · c + b · d) + a · c
                ≡⟨ +-commute ( (a · d + b · c + b · d)) (a · c) ⟩
                refl

  θProp : invPlus θ ≡ θ
  θProp = sym
          (begin
          θ ≡⟨ sym (+-inv₂ θ) ⟩ (θ + invPlus θ) ≡⟨ (θ-unit (invPlus θ)) ⟩ refl)


  assM : (a b c : A) → A
  assM a b c = ((a · b) · c) + invPlus (a · (b · c))

  associatorTheorem : (a b c : A) → (assM a b c ≡ θ) → ((a · b) · c) ≡ (a · (b · c))
  associatorTheorem a b c f = sym $
                      begin
                      (a · (b · c) ≡⟨ sym (θ-unit (a · b · c)) ⟩
                      (θ + a · b · c) ≡⟨ (cong-+ θ (assM a b c) (a · b · c) (sym f)) ⟩
                      assM a b c + a · b · c
                      ≡⟨ cong-+ (assM a b c) (((a · b) · c) + invPlus (a · (b · c))) (a · b · c) refl ⟩
                      (((a · b) · c + invPlus (a · b · c)) + a · b · c) ≡⟨ +-assoc ((a · b) · c) (invPlus (a · b · c)) (a · b · c) ⟩
                      ((a · b) · c + invPlus (a · b · c) + a · b · c) ≡⟨ (+-commute ((a · b) · c) (invPlus (a · b · c) + a · b · c)) ⟩
                      (((invPlus (a · b · c) + a · b · c) + (a · b) · c) ≡⟨ (cong-+ (invPlus (a · b · c) + a · b · c) θ ((a · b) · c) (+-inv₁ (a · b · c))) ⟩
                      θ-unit ((a · b) · c)))


  eq₁ : (a b c : A) → ((a + b) ≡ c) → (a ≡ (c + invPlus b))
  eq₁ a b c f = sym $
              begin
              (c + invPlus b)
              ≡⟨ (cong-+ c (a + b) (invPlus b) (sym f)) ⟩
              ((a + b) + invPlus b)
              ≡⟨ (+-assoc a b (invPlus b)) ⟩
              (a + b + invPlus b
              ≡⟨ +-commute a (b + invPlus b) ⟩
              (b + invPlus b) + a
              ≡⟨ cong-+ (b + invPlus b) θ a (+-inv₂ b) ⟩
              θ-unit a)

  eq₂ : (a b c : A) → ((a + b) ≡ c) → (b ≡ (c + invPlus a))
  eq₂ a b c f = sym $ begin
              ((c + invPlus a)
              ≡⟨ (cong-+ c (a + b) (invPlus a) (sym f)) ⟩
              ((a + b) + invPlus a
              ≡⟨ +-assoc a b (invPlus a) ⟩
              a + b + invPlus a
              ≡⟨ +-commute a (b + invPlus a) ⟩
              ((b + invPlus a) + a)
              ≡⟨ (+-assoc b (invPlus a) a) ⟩
              (b + invPlus a + a
              ≡⟨ +-commute b (invPlus a + a) ⟩
              (invPlus a + a) + b
              ≡⟨ cong-+ (invPlus a + a) θ b (+-inv₁ a) ⟩
              θ-unit b)))

  zeroProp : (a : A) → ((θ + a) ≡ θ) → a ≡ θ
  zeroProp a f = sym $
               begin
               (θ
               ≡⟨ sym f ⟩
               θ-unit a)


  zeroProp₁ : (a b : A) → ((a + b) ≡ a) → (b ≡ θ)
  zeroProp₁ a b f =
              b
              ≡⟨ eq₂ a b a f ⟩
              +-inv₂ a
              

  θProp₁ : (a : A) → a · θ ≡ θ
  θProp₁ a = begin
             (a · θ) ≡⟨ sym (+-θ (a · θ)) ⟩
             (a · θ + θ)
             ≡⟨ cong-+₁ θ (a · θ + (invPlus (a · θ))) (a · θ) (sym (+-inv₂ (a · θ))) ⟩
             (a · θ + a · θ + invPlus (a · θ))
             ≡⟨ sym (+-assoc (a · θ) (a · θ) (invPlus (a · θ))) ⟩
             ((a · θ + a · θ) + invPlus (a · θ))
             ≡⟨ cong-+ (a · θ + a · θ) (a · (θ + θ)) (invPlus (a · θ)) (sym (·-distr-right a θ θ)) ⟩
             (a · (θ + θ) + invPlus (a · θ))
             ≡⟨ cong-+ (a · (θ + θ)) (a · θ) (invPlus (a · θ)) ((a · (θ + θ)) ≡⟨ (cong-·₂ (θ + θ) θ a (+-θ θ)) ⟩ refl) ⟩
             +-inv₂ (a · θ)
             
open Ring {{...}} public

record AssociativeRing (A : Set){{R : Ring A}} : Set where
  constructor mkAssocRing
  field
    ·-assoc : (a b c : A) → (a · b · c) ≡ ((a · b) · c)
open AssociativeRing {{...}} public
  


record LeeRing (A : Set){{R : Ring A}} : Set where
  constructor mkLeeRing
  field
    leeAxiom₁ : (a : A) → (a · a) ≡ θ
    leeAxiom₂ : (a b c : A) → (((a · b) · c) + (b · (c · a)) + (c · (a · b))) ≡ θ

  lemma : (a b : A) → ((a + b) · (a + b)) ≡ ((a · b) + (b · a))
  lemma a b =
          (a + b) · (a + b)
          ≡⟨ distrLaw₁ a b a b ⟩
          (a · a + a · b + b · a + b · b)
          ≡⟨ cong-+ (a · a) θ (a · b + b · a + b · b) (leeAxiom₁ a) ⟩
          θ + a · b + b · a + b · b
          ≡⟨ θ-unit (a · b + b · a + b · b) ⟩
          a · b + b · a + b · b
          ≡⟨ sym (+-assoc (a · b) (b · a) (b · b)) ⟩
          (a · b + b · a) + b · b
          ≡⟨ +-commute (a · b + b · a) (b · b) ⟩
          (b · b + a · b + b · a)
          ≡⟨ (cong-+ (b · b) θ (a · b + b · a) (leeAxiom₁ b)) ⟩
          θ-unit (a · b + b · a)

  lemma₁ : (a b : A) → (a · b + b · a) ≡ θ
  lemma₁ a b = (a · b + b · a) ≡⟨ (sym (lemma a b)) ⟩ (leeAxiom₁ (a + b))

  anticommute : (a b : A) → (a · b) ≡ (invPlus (b · a))
  anticommute a b = a · b
                    ≡⟨ sym (θ-unit (a · b)) ⟩
                    θ + a · b
                    ≡⟨ cong-+ θ (invPlus (b · a) + (b · a)) (a · b) (sym (+-inv₁ (b · a))) ⟩
                    (invPlus (b · a) + b · a) + a · b
                    ≡⟨ +-assoc (invPlus (b · a)) (b · a) (a · b) ⟩
                    invPlus (b · a) + b · a + a · b
                    ≡⟨ +-commute (invPlus (b · a)) (b · a + a · b) ⟩
                    ((b · a + a · b) + invPlus (b · a))
                    ≡⟨ (cong-+ (b · a + a · b) θ (invPlus (b · a)) (lemma₁ b a)) ⟩
                    (θ-unit (invPlus (b · a)))
  
record BoolRing (A : Set){{Q : Ring A}}{{R : AssociativeRing A}} : Set where
  constructor mkBoolRing
  field
    imdepotency : (a : A) → (a · a) ≡ a

  xorLemma : (a b : A) → (a + b + a · b + b · a) ≡ (a + b)
  xorLemma a b = sym $
             begin
             a + b
             ≡⟨ sym (imdepotency (a + b)) ⟩
             (a + b) · (a + b)
             ≡⟨ distrLaw₁ a b a b ⟩
             a · a + a · b + b · a + b · b
             ≡⟨ cong-+ (a · a) a (a · b + b · a + b · b) (imdepotency a) ⟩
             a + a · b + b · a + b · b
             ≡⟨ sym (+-assoc a (a · b) (b · a + b · b))  ⟩
             (a + a · b) + b · a + b · b
             ≡⟨ sym (+-assoc ((a + a · b)) (b · a) (b · b)) ⟩
             ((a + a · b) + b · a) + b · b
             ≡⟨ +-commute (((a + a · b) + b · a)) (b · b) ⟩
             b · b + ((a + a · b) + b · a) 
             ≡⟨ cong-+ (b · b) b ((a + a · b) + b · a) (imdepotency b) ⟩
             b + (a + a · b) + b · a
             ≡⟨ sym (+-assoc b  (a + a · b) (b · a)) ⟩
             (b + (a + a · b)) + b · a
             ≡⟨ cong-+ (b + (a + a · b)) (b + a + a · b) (b · a) refl ⟩
             ((b + a + a · b) + b · a)
             ≡⟨ (cong-+ (b + a + a · b) (a + b + a · b) (b · a)
             ((b + a + a · b) ≡⟨ (sym (+-assoc b a (a · b))) ⟩
             ((b + a) + a · b)
             ≡⟨ (cong-+ (b + a) (a + b) (a · b) (+-commute b a)) ⟩
             ((a + b) + a · b)
             ≡⟨ +-assoc a b (a · b) ⟩
             refl)) ⟩
             ((a + b + a · b) + b · a)
             ≡⟨ +-assoc a (b + a · b) (b · a) ⟩
             a + (b + a · b) + b · a
             ≡⟨ +-commute a ((b + a · b) + b · a) ⟩
             (((b + a · b) + b · a) + a)
             ≡⟨ (cong-+ ((b + a · b) + b · a) (b + a · b + b · a) a (((b + a · b) + b · a) ≡⟨ +-assoc b (a · b) (b · a) ⟩
             refl)) ⟩
             (b + a · b + b · a) + a
             ≡⟨ +-commute (b + a · b + b · a) a ⟩
             refl

  imdepotentCollorary : (a b : A) → (a · b + b · a) ≡ θ
  imdepotentCollorary a b = zeroProp₁ (a + b) (a · b + b · a)
                            (begin (((a + b) + (a · b + b · a))
                            ≡⟨ +-assoc a b (a · b + b · a) ⟩
                            xorLemma a b))

  xor : (a : A) → (a + a) ≡ θ
  xor a = begin
          a + a
          ≡⟨ cong-+ a (a · a) a (sym (imdepotency a)) ⟩
          (a · a + a)
          ≡⟨ (+-commute (a · a) a) ⟩
          ((a + a · a)
          ≡⟨ (cong-+ a (a · a) (a · a) (sym (imdepotency a))) ⟩
          (imdepotentCollorary a a))

  invBooleProp : (a : A) → a ≡ invPlus a
  invBooleProp a = begin
               (a
               ≡⟨ sym (imdepotency a) ⟩
               (a · a)
               ≡⟨ (cong-·₁ a (a + invPlus a + a) a (sym ((a + invPlus a + a) ≡⟨ (sym (+-assoc a (invPlus a) a)) ⟩
               ((a + invPlus a) + a) ≡⟨ (cong-+ (a + invPlus a) θ a (+-inv₂ a)) ⟩ θ-unit a))) ⟩
               (a + invPlus a + a) · a
               ≡⟨ cong-·₂ a (a + invPlus a + a) (a + invPlus a + a) ((sym ((a + invPlus a + a) ≡⟨ (sym (+-assoc a (invPlus a) a)) ⟩
               ((a + invPlus a) + a) ≡⟨ (cong-+ (a + invPlus a) θ a (+-inv₂ a)) ⟩ θ-unit a))) ⟩
               (a + invPlus a + a) · (a + invPlus a + a)
               ≡⟨ imdepotency (a + invPlus a + a) ⟩
               (a + invPlus a + a)
               ≡⟨ (+-commute a (invPlus a + a)) ⟩
               ((invPlus a + a) + a)
               ≡⟨ (+-assoc (invPlus a) a a) ⟩
               (invPlus a + a + a
               ≡⟨ +-commute (invPlus a) (a + a) ⟩
               ((a + a) + invPlus a)
               ≡⟨ (cong-+ (a + a) θ (invPlus a) (xor a)) ⟩
               θ-unit (invPlus a)))

  commutative : (a b : A) → (a · b) ≡ (b · a)
  commutative a b = begin
                    ((a · b)
                    ≡⟨ sym (θ-unit (a · b)) ⟩
                    (θ + a · b)
                    ≡⟨ (cong-+ θ (a · b + b · a) (a · b) (sym (imdepotentCollorary a b))) ⟩
                    ((a · b + b · a) + a · b
                    ≡⟨ +-commute (a · b + b · a) (a · b) ⟩
                    (a · b + a · b + b · a)
                    ≡⟨ sym (+-assoc (a · b) (a · b) (b · a)) ⟩
                    (a · b + a · b) + b · a
                    ≡⟨ cong-+ (a · b + a · b) θ (b · a) (xor (a · b)) ⟩
                    θ-unit (b · a)))
  
        
  

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

