module Maybe where

open import Equality
open import CategoryStructure
open import Function
open import UnitAndEmpty
open import Product

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

maybe-elim : {A B : Set} → B → (A → B) → Maybe A → B
maybe-elim y f Nothing = y
maybe-elim y f (Just x) = f x


functorMaybe : Functor Maybe
functorMaybe = mkFunctor fmap fmap-id fmap-∘ where
  fmap : ∀ {A B} → (A → B) → Maybe A → Maybe B
  fmap f Nothing = Nothing
  fmap f (Just x) = Just (f x)

  fmap-id : {A : Set}(fx : Maybe A) → fmap id fx ≡ id fx
  fmap-id Nothing = refl
  fmap-id (Just x) = refl
  
  fmap-∘ : {A B C : Set}{f : A → B}{g : B → C}(fx : Maybe A) → fmap (g ∘ f) fx ≡ (fmap g ∘ fmap f) fx
  fmap-∘ Nothing = refl
  fmap-∘ (Just x) = refl

applicativeMaybe : Applicative Maybe
applicativeMaybe = mkApplicative pure (_<*>_) pure-id <*>-∘ hom_law app_pure_law where
  pure : ∀ {A} → A → Maybe A
  pure x = Just x

  _<*>_ : ∀ {A B} → Maybe (A → B) → Maybe A → Maybe B
  Nothing <*> Nothing = Nothing
  (Just f) <*> Nothing = Nothing
  Nothing <*> (Just x) = Nothing
  (Just f) <*> (Just x) = Just (f x)

  pure-id : ∀ {A} → (fx : Maybe A) → ((pure id) <*> fx) ≡ fx
  pure-id Nothing = refl
  pure-id (Just x) = refl
  
  <*>-∘ : ∀ {A B C} → (f : Maybe (A → B))(g : Maybe (B → C))(x : Maybe A) → (((pure (λ f g → f ∘ g) <*> g) <*> f) <*> x) ≡ (g <*> (f <*> x))
  <*>-∘ Nothing Nothing Nothing = refl
  <*>-∘ Nothing Nothing (Just x) = refl
  <*>-∘ Nothing (Just f) Nothing = refl
  <*>-∘ Nothing (Just f) (Just x) = refl
  <*>-∘ (Just f) Nothing Nothing = refl
  <*>-∘ (Just f) Nothing (Just x) = refl
  <*>-∘ (Just f) (Just x) Nothing = refl
  <*>-∘ (Just f) (Just x) (Just x₁) = refl
  
  hom_law : ∀ {A B}(f : A → B)(x : A) → (pure f <*> pure x) ≡ pure (f x)
  hom_law f x = refl
  
  app_pure_law : ∀ {A B}(f : Maybe (A → B))(x : A) → (f <*> pure x) ≡ (pure (λ f → f $ x) <*> f)
  app_pure_law Nothing x = refl
  app_pure_law (Just f) x = refl


monad' = mkMonad return join assoc unity-left unity-right
                 naturality-return naturality-join
  where
    return : {A : Set} → A → Maybe A
    return = Just

    join : {A : Set} → Maybe (Maybe A) → Maybe A
    join (Just mx) = mx
    join Nothing   = Nothing

    open Functor functorMaybe

    assoc : {A : Set} (mmmx : Maybe (Maybe (Maybe A))) →
                    join (join mmmx) ≡ join (fmap join mmmx)
    assoc (Just _) = refl
    assoc Nothing  = refl

    unity-left : {A : Set} (mx : Maybe A) → join (return mx) ≡ mx
    unity-left _ = refl

    unity-right : {A : Set} (mx : Maybe A) → join (fmap return mx) ≡ mx
    unity-right (Just _) = refl
    unity-right Nothing  = refl

    naturality-return : {A B : Set} (f : A → Maybe B) (x : A) →
                        return (f x) ≡ fmap f (return x)
    naturality-return f x = refl

    naturality-join : {A B : Set} {f : A → Maybe B} (mmx : Maybe (Maybe A)) →
                      join (fmap (fmap f) mmx) ≡ fmap f (join mmx)
    naturality-join Nothing = refl
    naturality-join (Just x) = refl

kleisliMaybe : KleisliTriple Maybe
kleisliMaybe = mkKleisli return bind assoc-bind unity-left-bind unity-right-bind
  where
    return : ∀ {A} → A → Maybe A
    return = Just

    bind : ∀ {A B} → (A → Maybe B) → Maybe A → Maybe B
    bind f Nothing = Nothing
    bind f (Just x) = f x

    assoc-bind : ∀ {A B C} → (f : A → Maybe B) → (g : B → Maybe C) → (mx : Maybe A) → bind g (bind f mx) ≡ bind (bind g ∘ f) mx
    assoc-bind f g Nothing = refl
    assoc-bind f g (Just x) = refl
    
    unity-left-bind : ∀ {A B} → (f : A → Maybe B) → (x : A) → bind f (return x) ≡ f x
    unity-left-bind f x = refl

    unity-right-bind : ∀ {A}(mx : Maybe A) → bind return mx ≡ mx
    unity-right-bind Nothing = refl
    unity-right-bind (Just x) = {!refl!}

