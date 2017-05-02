module CategoryStructure where

open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)
open import AlgebraStructures
open import Identity

record Functor (F : Set → Set) : Set₁ where
  constructor mkFunctor
  infixl 4 _<$>_ _<$_
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set}(fx : F A) → fmap id fx ≡ id fx
    fmap-∘ : {A B C : Set}{f : A → B}{g : B → C}(fx : F A) → fmap (g ∘ f) fx ≡ (fmap g ∘ fmap f) fx
  _<$>_ : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap
  _<$_ : ∀ {A B} → A → F B → F A
  _<$_ = fmap ∘ const
  _$>_ : ∀ {A B} → F A → B → F B
  _$>_ = flip (fmap ∘ const)

record Applicative (F : Set → Set) : Set₁ where
  constructor mkApplicative
  infixl 2 _<*>_ _<**>_ _<*_ _*>_
  field
    pure : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    pure-id : ∀ {A} → (fx : F A) → ((pure id) <*> fx) ≡ fx
    <*>-∘ : ∀ {A B C} → (f : F (B → C))(g : F (A → B))(x : F A) → (pure (λ f g → f ∘ g) <*> f <*> g <*> x) ≡ (f <*> (g <*> x)) 
    hom_law : ∀ {A B}(f : A → B)(x : A) → (pure f <*> pure x) ≡ pure (f x)
    app_pure_law : ∀ {A B}(f : F (A → B))(x : A) → (f <*> pure x) ≡ (pure (λ f → f $ x) <*> f)
  liftA : ∀ {A B} → (A → B) → F A → F B
  liftA f x = (pure f) <*> x
  liftA₂ : ∀ {A B C} → (A → B → C) → F A → F B → F C
  liftA₂ f x y = (pure f) <*> x <*> y
  liftA₃ : ∀ {A B C D} → (A → B → C → D) → F A → F B → F C → F D
  liftA₃ f x y z = (pure f) <*> x <*> y <*> z
  _<*_ : ∀ {A B} → F A → F B → F A
  _<*_ = liftA₂ $ const
  _*>_ : ∀ {A B} → F A → F B → F B
  x *> y = (liftA₂ $ const id) x y
  _<**>_ : ∀ {A B} → F A → F (A → B) → F B
  _<**>_ = liftA₂ (flip (_$_))

record Alternative (F : Set → Set){{FF : Functor F}}{{app : Applicative F}} : Set₁ where
  constructor mkAlternative
  infixl 3 _<|>_
  open Applicative app
  open Functor FF
  field
    empty : ∀ {A} → F A
    _<|>_ : ∀ {A} → F A → F A → F A
    empty_unit₁ : ∀ {A}(fx : F A) → (fx <|> empty) ≡ fx
    empty_unit₂ : ∀ {A}(fx : F A) → (empty <|> fx) ≡ fx
    assoc-<|> : ∀ {A} (fx gx hx : F A) → ((fx <|> gx) <|> hx) ≡ (fx <|> (gx <|> hx))

record Foldable (T : Set → Set) : Set₁ where
  constructor mkFoldable
  field
    foldMap : ∀ {A M}{AM : Monoid M} → (A → M) → (T A) → M
    -- foldMaplaw : ∀ {A B M}{AM : Monoid M} → (f : B → M)(g : A → B)(x : T A) → ((foldMap (g ∘ f)) x) ≡ ((g ∘ (foldMap f)) x) 

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
    naturality-join : ∀ {A B}{f : A → F B}(mmx : F ( F A ))→ join (fmap (fmap f) mmx) ≡ fmap f (join mmx)
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
    mzero-unit₂ : ∀ {A}(mx : F A) → (mplus mx mzero) ≡ mx
    assoc : ∀ {A}(fx gx hx : F A) → (mplus (mplus fx gx) hx) ≡ (mplus fx (mplus gx hx))

record MonadTrans (F : Set → Set) (kl : KleisliTriple F) : Set₁ where
  constructor mkMonadTrans
  open KleisliTriple kl
  field
    lift : ∀ {A}{G : Set → Set}{AG : KleisliTriple G} → G A → F (G A)


{- data Compose (A : Set)(F G : Set → Set) : Set₁ where
  compose : F (G A) → Compose F G A
  getCompose : Compose F G A → F (G A) -}
