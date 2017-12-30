module LinearAlgebra where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.Vec as Vec
open import Data.Product
open import Data.Nat hiding (_+_)
open import Data.List as List
open import Data.Bool
open import Data.Vec.All as VA
open import Data.Fin hiding (_+_)
open import Data.String
open import Function


record Field (A : Set) : Set where
  constructor mkField
  infixr 5 _+_
  infixr 6 _·_
  field
    _+_ : A → A → A
    _·_ : A → A → A 
    invPlus : A → A
    invMult : A → A
    ε : A
    θ : A 
    +-assoc : (a b c : A) → a + b + c ≡ (a + b) + c
    +-comm : (a b : A) → a + b ≡ b + a
    +-inv : (a : A) → a + invPlus a ≡ θ
    +-θ : (a : A) → a + θ ≡ a
    ·-assoc : (a b c : A) → a · b · c ≡ (a · b) · c
    ·-comm : (a b : A) → a · b ≡ b · a
    ·-inv : (a : A) → a · invMult a ≡ ε
    ·-ε : (a : A) → a · ε ≡ a
    distr : (a b c : A) → a · (b + c) ≡ a · b + a · c

  mult : A → A → A
  mult x y = x · y

  lemma-+eq₁ : (a b c : A) → (a ≡ b) → a + c ≡ b + c
  lemma-+eq₁ a b c refl = refl

  lemma-+eq₂ : (a b c : A) → (a ≡ b) → c + a ≡ c + b
  lemma-+eq₂ a b c refl = refl

  lemma-eq₁ : (a b c : A) → (a ≡ b) → a · c ≡ b · c
  lemma-eq₁ a b c refl = refl

  lemma-eq₂ : (a b c : A) → (a ≡ b) → c · a ≡ c · b
  lemma-eq₂ a b c refl = refl


  θ-fact : (a : A) → a · θ ≡ θ
  θ-fact a = begin
             (a · θ
             ≡⟨ sym (+-θ (a · θ)) ⟩
             a · θ + θ
             ≡⟨ lemma-+eq₂ θ (a · θ + invPlus (a · θ)) (a · θ) (sym (+-inv (a · θ))) ⟩
             a · θ + a · θ + invPlus (a · θ)
             ≡⟨ +-assoc (a · θ) (a · θ) (invPlus (a · θ)) ⟩
             (a · θ + a · θ) + invPlus (a · θ)
             ≡⟨ lemma-+eq₁ (a · θ + a · θ) (a · (θ + θ)) (invPlus (a · θ)) (sym (distr a θ θ)) ⟩
             a · (θ + θ) + invPlus (a · θ)
             ≡⟨ lemma-+eq₁ (a · (θ + θ)) (a · θ) (invPlus (a · θ)) (lemma-eq₂ (θ + θ) θ a (+-θ θ)) ⟩
             +-inv (a · θ))

  

open Field{{...}} public

record VectorSpace (V : Set) (A : Set) {{F : Field A}} : Set where
  constructor mkVectorSpace
  infixr 5 _|+|_
  infixr 6 _|·|_
  field
    _|+|_ : V → V → V 
    _|·|_ : A → V → V
    |θ| : V
    invVect : V → V
    assoc-Vect : (a b c : V) → a |+| b |+| c ≡ (a |+| b) |+| c
    comm-Vect : (a b : V) → a |+| b ≡ b |+| a
    inv-|+| : (a : V) → a |+| invVect a ≡ |θ|
    |+|-|θ| : (a : V) → a |+| |θ| ≡ a
    ·-|·| : (a b : A) → (c : V) → (a · b) |·| c ≡ a |·| b |·| c
    ε-|·| : (a : V) → ε |·| a ≡ a
    |+|-|·| : (a : A) → (b c : V) → a |·| (b |+| c) ≡ a |·| b |+| a |·| c
    +-|·| : (a b : A) → (c : V) → (a + b) |·| c ≡ a |·| c |+| b |·| c

  infixr 6 _|-|_
  _|-|_ : V → V → V
  _|-|_ x y = x |+| invVect y

  infixr 7 _∶_
  _∶_ : A → V → V
  x ∶ y = (invMult x) |·| y

  vMult : A → V → V
  vMult a b = a |·| b


  linearCombination : ∀ {n} → Vec A n → Vec V n → V
  linearCombination [] [] = |θ|
  linearCombination (x ∷ xs) (y ∷ ys) = (x |·| y) |+| linearCombination xs ys

  prop : (a b c : V) → (a ≡ b) → (a |+| c) ≡ (b |+| c)
  prop a b c refl = refl

  prop₁ : (a b c : V) → (a ≡ b) → (c |+| a) ≡ (c |+| b)
  prop₁ a b c refl = refl

  prop4₁ : (a b c d e : V) → (d ≡ e) → (a |+| b |+| c |+| d) ≡ (a |+| b |+| c |+| e)
  prop4₁ a b c d e refl = refl

  prop₂ : (a b c : V) → a |+| b ≡ c → a ≡ c |-| b
  prop₂ a b c f = begin (sym  (c |-| b ≡⟨ refl ⟩
                  (c |+| invVect b) ≡⟨ prop c (a |+| b) (invVect b) (sym f) ⟩
                  ((a |+| b) |+| invVect b) ≡⟨ sym (assoc-Vect a b (invVect b)) ⟩
                  a |+| b |+| invVect b ≡⟨ prop₁ (b |+| invVect b) |θ| a (inv-|+| b) ⟩ |+|-|θ| a))

  prop₃ : (a b : A) → (v : V) → a ≡ b → a |·| v ≡ b |·| v
  prop₃ a b c refl = refl

  prop₄ : (a : A) → (v w : V) → (v ≡ w) → a |·| v ≡ a |·| w
  prop₄ a v w refl = refl

  fact₁ : (a : V) → θ |·| a ≡ |θ|
  fact₁ a = begin
            ((θ |·| a) ≡⟨ sym (|+|-|θ| (θ |·| a)) ⟩
            θ |·| a |+| |θ|
            ≡⟨ prop₁ |θ| (θ |·| a |+| invVect (θ |·| a)) (θ |·| a) (sym (inv-|+| (θ |·| a))) ⟩
            θ |·| a |+| θ |·| a |+| invVect (θ |·| a)
            ≡⟨ assoc-Vect (θ |·| a) (θ |·| a) (invVect (θ |·| a)) ⟩
            (θ |·| a |+| θ |·| a) |+| invVect (θ |·| a)
            ≡⟨ prop (θ |·| a |+| θ |·| a) ((θ + θ) |·| a) (invVect (θ |·| a)) (sym (+-|·| θ θ a)) ⟩
            ((θ + θ) |·| a |+| invVect (θ |·| a))
            ≡⟨ prop ((θ + θ) |·| a) (θ |·| a) (invVect (θ |·| a)) (prop₃ (θ + θ) θ a (+-θ θ)) ⟩
            inv-|+| (θ |·| a))

  fact₂ : (a : A) → a |·| |θ| ≡ |θ|
  fact₂ a = a |·| |θ| ≡⟨ prop₄ a |θ| (θ |·| |θ|) (sym (fact₁ |θ|)) ⟩ a |·| θ |·| |θ| ≡⟨ sym (·-|·| a θ |θ|) ⟩
                      (a · θ) |·| |θ| ≡⟨ prop₃ (a · θ) θ |θ| (θ-fact a) ⟩
                      fact₁ |θ|

  divLemma : (a : A) → (v w : V) → a |·| v ≡ w → v ≡ (invMult a) |·| w
  divLemma a v w f = sym $ begin
                     ((invMult a) |·| w
                     ≡⟨ prop₄ (invMult a) w (a |·| v) (sym f) ⟩
                     (invMult a) |·| a |·| v
                     ≡⟨ sym (·-|·| (invMult a) a v) ⟩
                     ((invMult a) · a) |·| v
                     ≡⟨ prop₃ ((invMult a) · a) ε v (trans (·-comm (invMult a) a) (·-inv a)) ⟩
                     ε-|·| v)

  fact₃ : (a b c : V) → (a |+| b ≡ c) → (b ≡ c |-| a)
  fact₃ a b c f = sym $ begin
                  c |-| a
                  ≡⟨ refl ⟩
                  c |+| invVect a
                  ≡⟨ prop c (a |+| b) (invVect a) (sym f) ⟩
                  (a |+| b) |+| invVect a
                  ≡⟨ prop (a |+| b) (b |+| a) (invVect a) (comm-Vect a b) ⟩
                  (b |+| a) |+| invVect a
                  ≡⟨ sym (assoc-Vect b  a (invVect a)) ⟩
                  b |+| a |+| invVect a
                  ≡⟨ prop₁ (a |+| invVect a) |θ| b (inv-|+| a) ⟩
                  |+|-|θ| b


  invVect-ε : (v : V) → invVect v ≡ (invPlus ε) |·| v
  invVect-ε v = {!!}

  LinearDependence : (n : ℕ) → Vec V n → Set 
  LinearDependence n x = Σ (Vec A n) λ val → linearCombination val x ≡ |θ|


  divideVec : {n : ℕ} → (a : A) → Vec V n → Vec V n
  divideVec val xs = Vec.map (vMult (invMult val)) xs

  propVec : {n : ℕ} → (xs : Vec A n) → (ys : Vec V n) → (invPlus ε) |·| (linearCombination xs ys) ≡ linearCombination (Vec.map (mult (invPlus ε)) xs) ys
  propVec [] [] = begin
                  ((invPlus ε) |·| (linearCombination [] [])) ≡⟨ prop₄ (invPlus ε) (linearCombination [] []) |θ| refl ⟩
                  fact₂ (invPlus ε)
  propVec (x ∷ xs) (y ∷ ys) = begin
                              ((invPlus ε) |·| linearCombination (x ∷ xs) (y ∷ ys)
                              ≡⟨ refl ⟩
                              (invPlus ε) |·| (x |·| y |+| linearCombination xs ys)
                              ≡⟨ |+|-|·| (invPlus ε) (x |·| y) (linearCombination xs ys) ⟩
                              (invPlus ε) |·| x |·| y |+| (invPlus ε) |·| linearCombination xs ys
                              ≡⟨ prop₁ ((invPlus ε) |·| linearCombination xs ys) (linearCombination (Vec.map (mult (invPlus ε)) xs) ys) ((invPlus ε) |·| x |·| y) (propVec xs ys) ⟩
                              (invPlus ε) |·| x |·| y |+| linearCombination (Vec.map (mult (invPlus ε)) xs) ys
                              ≡⟨ prop ((invPlus ε) |·| x |·| y) (((invPlus ε) · x) |·| y) (linearCombination (Vec.map (mult (invPlus ε)) xs) ys) (sym (·-|·| (invPlus ε) x y)) ⟩
                              refl)

  theorem₁ : {n : ℕ} → (xs : Vec A n) → (ys : Vec V n) → (v : V) → v ≡ linearCombination xs ys → LinearDependence (suc n) (v ∷ ys)
  theorem₁ [] [] v f = (θ ∷ []) , (linearCombination (θ ∷ []) (v ∷ [])
                                  ≡⟨ refl ⟩ θ |·| v |+| linearCombination [] []
                                  ≡⟨ prop (θ |·| v) |θ| (linearCombination [] []) (fact₁ v) ⟩
                                  |θ| |+| linearCombination [] []
                                  ≡⟨ prop₁ (linearCombination [] []) |θ| |θ| refl ⟩
                                  |+|-|θ| |θ|)
  theorem₁ (x ∷ xs) (y ∷ ys) v f = invPlus ε ∷ (x ∷ xs) ,
                                   (linearCombination (invPlus ε ∷ (x ∷ xs)) ((v ∷ y ∷ ys))
                                   ≡⟨ refl ⟩
                                   invPlus ε |·| v |+| linearCombination (x ∷ xs) (y ∷ ys)
                                   ≡⟨ prop (invPlus ε |·| v) (invPlus ε |·| linearCombination (x ∷ xs) (y ∷ ys)) (linearCombination (x ∷ xs) (y ∷ ys))
                                   (prop₄ (invPlus ε) v (linearCombination (x ∷ xs) (y ∷ ys)) f) ⟩
                                   invPlus ε |·| linearCombination (x ∷ xs) (y ∷ ys) |+| linearCombination (x ∷ xs) (y ∷ ys)
                                   ≡⟨ prop₁ (linearCombination (x ∷ xs) (y ∷ ys)) (ε |·| linearCombination (x ∷ xs) (y ∷ ys))
                                   (invPlus ε |·| linearCombination (x ∷ xs) (y ∷ ys)) (sym (ε-|·| (linearCombination (x ∷ xs) (y ∷ ys)))) ⟩
                                   invPlus ε |·| linearCombination (x ∷ xs) (y ∷ ys) |+| ε |·| linearCombination (x ∷ xs) (y ∷ ys)
                                   ≡⟨ sym (+-|·| (invPlus ε) ε (linearCombination (x ∷ xs) (y ∷ ys))) ⟩
                                   (invPlus ε + ε) |·| linearCombination (x ∷ xs) (y ∷ ys)
                                   ≡⟨ prop₃ (invPlus ε + ε) θ (linearCombination (x ∷ xs) (y ∷ ys))
                                   ( trans (+-comm (invPlus ε) ε) (+-inv ε)) ⟩
                                   fact₁ (linearCombination (x ∷ xs) (y ∷ ys)))


  lemma-express : {n : ℕ} → (xs : Vec A n) → (ys : Vec V n) → (x : A) → (y : V) → linearCombination (x ∷ xs) (y ∷ ys) ≡ |θ| → x |·| y ≡ (invPlus ε) |·| linearCombination xs ys
  lemma-express xs ys val vec f = begin
                                  val |·| vec
                                  ≡⟨ prop₂ (val |·| vec) (linearCombination xs ys) |θ| f ⟩
                                  |θ| |-| linearCombination xs ys
                                  ≡⟨ refl ⟩
                                  |θ| |+| invVect (linearCombination xs ys)
                                  ≡⟨ prop₁ (invVect (linearCombination xs ys)) ((invPlus ε) |·| linearCombination xs ys) |θ| (invVect-ε (linearCombination xs ys)) ⟩
                                  |θ| |+| (invPlus ε) |·| linearCombination xs ys
                                  ≡⟨ comm-Vect |θ| ((invPlus ε) |·| linearCombination xs ys) ⟩
                                  (invPlus ε) |·| linearCombination xs ys |+| |θ|
                                  ≡⟨ |+|-|θ| ((invPlus ε) |·| linearCombination xs ys) ⟩
                                  refl
                                  
                                  


  theorem₂ : {n : ℕ} → (xs : Vec A n) → (ys : Vec V n) → (x : A) → (y : V) → linearCombination (x ∷ xs) (y ∷ ys) ≡ |θ| → y ≡ ((invPlus ε) · (invMult x)) |·| linearCombination xs ys
  theorem₂ xs ys val vec f = begin sym
                           (((invPlus ε) · (invMult val)) |·| linearCombination xs ys
                           ≡⟨ prop₃ ((invPlus ε) · (invMult val)) ((invMult val) · (invPlus ε)) (linearCombination xs ys) (·-comm (invPlus ε) (invMult val)) ⟩
                           ((invMult val) · (invPlus ε)) |·| linearCombination xs ys
                           ≡⟨ ·-|·| (invMult val) (invPlus ε) (linearCombination xs ys) ⟩
                           (invMult val) |·| (invPlus ε) |·| linearCombination xs ys
                           ≡⟨ prop₄ (invMult val) ((invPlus ε) |·| linearCombination xs ys) (val |·| vec) (sym (lemma-express xs ys val vec f)) ⟩
                           (invMult val) |·| val |·| vec
                           ≡⟨ sym (·-|·| (invMult val) val vec) ⟩
                           (invMult val · val) |·| vec
                           ≡⟨ prop₃ (invMult val · val) ε vec (trans (·-comm (invMult val) val) (·-inv val)) ⟩
                           ε-|·| vec)
                                                                                                                                                                           
  _⇔_ : Set → Set → Set
  P ⇔ Q = (P → Q) × (Q → P)

  infixr 0 _⇔_

  LinearIndependence : (n : ℕ) → Vec V n → Set
  LinearIndependence n x = Σ (Vec A n) λ val → (linearCombination val x ≡ |θ|) ⇔ ((i : Fin n) → (Vec.lookup i val) ≡ θ )

  data Basis : (n : ℕ) → (xs : Vec V n) → Set where
    basis : (n : ℕ) → (xs : Vec V n) → LinearIndependence n xs → ((v : V) → Σ (Vec A n) (λ val → v ≡ linearCombination val xs)) → Basis n xs

  dimension : {n : ℕ} → {xs : Vec V n} → Basis n xs → ℕ
  dimension (basis n xs x x₁) = n
  
open VectorSpace{{...}} public


record Tensor (V : Set)(W : Set){{A : Set}}{{F : Field A}}{{v : VectorSpace V A}}{{w : VectorSpace W A}}{{v×w : VectorSpace (V × W) A}} : Set where
  constructor mkTensor
  infixr 7 _⊗_
  field
    _⊗_ : V → W → (V × W)
    {-distr₁ : (v₁ v₂ : V) → (w : W) → (v₁ |+| v₂) ⊗ w ≡ (v₁ ⊗ w) |+| (v₂ ⊗ w) -}
open Tensor{{...}} public
