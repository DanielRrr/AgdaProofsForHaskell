module CategoryStructure where

open import Function

infix 4 _≡_
data _≡_ {α}{A : Set α}(x : A) : A → Set where
  refl : x ≡ x

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

record Traversable (F : Set → Set) (app : Applicative F) : Set₁ where
  constructor mkTraversable
  open Applicative app
  field
    traverse : ∀ {A B}{G : Set → Set}{AG : Applicative G} → (A → F B) → G A → F (G B)

record Alternative (F : Set → Set) (app : Applicative F) : Set₁ where
  constructor mkAlternative
  infixl 3 _<|>_
  open Applicative app
  field
    empty : ∀ {A} → F A
    _<|>_ : ∀ {A} → F A → F A → F A
    empty_unit₁ : ∀ {A}(fx : F A) → (fx <|> empty) ≡ fx
    empty_unit₂ : ∀ {A}(fx : F A) → (empty <|> fx) ≡ fx
    assoc-<|> : ∀ {A} (fx gx hx : F A) → ((fx <|> gx) <|> hx) ≡ (fx <|> (gx <|> hx)) 

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
  bind : ∀ {A B} → (A → F B) → F A → F B
  bind f = join ∘ fmap f

record KleisliTriple (F : Set → Set) : Set₁ where
  constructor mkKleisli 
  field
    return : ∀ {A} → A → F A
    bind : ∀ {A B} → (A → F B) → F A → F B
    assoc-bind : ∀ {A B C} → (f : A → F B) → (g : B → F C) → (mx : F A) → bind g (bind f mx) ≡ bind (bind g ∘ f) mx
    unity-left-bind : ∀ {A B} → (f : A → F B) → (x : A) → bind f (return x) ≡ f x
    unity-right-bind : ∀ {A}(mx : F A) → bind return mx ≡ mx
  infixr 1 _=<<_
  _=<<_ : ∀ {A B} → (A → F B) → F A → F B
  f =<< x = bind f x
  infixl 1 _>>=_ _>>_
  _>>=_ : ∀ {A B} → F A → (A → F B) → F B
  _>>=_ = flip bind
  _>>_ : ∀ {A B} → F A → F B → F B
  mx >> my = mx >>= (const my)

record MonadPlus (F : Set → Set) (kl : KleisliTriple F) : Set₁ where
  constructor mkMonadPlus
  open KleisliTriple kl
  field
    mzero : ∀ {A} → F A
    mplus : ∀ {A} → F A → F A → F A
    mzero-unit₁ : ∀ {A}(mx : F A) → (mplus mzero mx) ≡ mx
    mzero-unit₂ : ∀ {A}(fx gx hx : F A) → (mplus (mplus fx gx) hx) ≡ (mplus fx (mplus gx hx))
    



  
