module CategoryStructure where

open import Function using (id; _∘_)

infix 4 _≡_
data _≡_ {α}{A : Set α}(x : A) : A → Set where
  refl : x ≡ x

infixl 0 _$_
_$_ : ∀ {α β}
      → {A : Set α} {B : A → Set β}
      → (f : (x : A) → B x)
      → ((x : A) → B x)
f $ x = f x

record Functor (F : Set → Set) : Set₁ where
  constructor mkFunctor
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set}(fx : F A) → fmap id fx ≡ id fx
    fmap-∘ : {A B C : Set}{f : A → B}{g : B → C}(fx : F A) → fmap (g ∘ f) fx ≡ (fmap g ∘ fmap f) fx


record Applicative (F : Set → Set) : Set₁ where
  constructor mkApplicative
  infixl 2 _<*>_
  field
    pure : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    pure-id : ∀ {A} → (fx : F A) → ((pure id) <*> fx) ≡ fx
    <*>-∘ : ∀ {A B C} → (f : F (A → B))(g : F (B → C))(x : F A) → (((pure (λ f g → f ∘ g) <*> g) <*> f) <*> x) ≡ (g <*> (f <*> x))
    hom_law : ∀ {A B}(f : A → B)(x : A) → (pure f <*> pure x) ≡ pure (f x)
    app_pure_law : ∀ {A B}(f : F (A → B))(x : A) → (f <*> pure x) ≡ (pure (λ f → f $ x) <*> f)


record Monad (F : Set → Set) (functor : Functor F) : Set₁ where
  constructor mkMonad
  open Functor functor using (fmap)
  field
    return : ∀ {A} → A → F A
    join : ∀ {A} → F (F A) → F A
    assoc : ∀ {A}(3mx : F (F (F A))) → join (join 3mx) ≡ join (fmap join 3mx)
    unity-left : ∀ {A}(mx : F A) → join (return mx) ≡ mx
    unity-right : ∀ {A}(mx : F A) → join (fmap return mx) ≡ mx
    naturality-return : ∀ {A B} (f : A → F B)(x : A) → return (f x) ≡ fmap f (return x)
