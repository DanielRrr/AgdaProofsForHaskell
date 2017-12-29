module Ring where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function


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
