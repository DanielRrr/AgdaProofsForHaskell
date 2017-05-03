module ListLaws where

open import CategoryStructure
open import AlgebraStructures
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)
open import Function
open import Data.List

functorList : Functor List
functorList = mkFunctor fmap fmap-id fmap-∘ where
  fmap : ∀ {A B} → (A → B) → List A → List B
  fmap f [] = []
  fmap f (x ∷ x₁) = (f x) ∷ fmap f x₁

  fmap-id : {A : Set}(fx : List A) → fmap id fx ≡ id fx
  fmap-id [] = refl
  fmap-id (x ∷ xs) = cong (_∷_ x) (fmap-id xs)

  fmap-∘ : {A B C : Set}{f : A → B}{g : B → C}(fx : List A) → fmap (g ∘ f) fx ≡ (fmap g ∘ fmap f) fx
  fmap-∘ [] = refl
  fmap-∘ {f = f}{g} (x ∷ xs) = cong (_∷_ (g (f x))) (fmap-∘ xs)

monoidList : ∀ {A} → Monoid (List A)
monoidList = mkMonoid ε _●_  ε-unit₁  ε-unit₂ assoc-Monoid where
  ε : ∀ {A} → List A
  ε = []

  _●_ : ∀ {A} → List A → List A → List A
  [] ● xs = xs
  (x ∷ xs) ● ys = x ∷ (xs ● ys)

  ε-unit₁ : ∀ {A} → (x : List A) → (x ● []) ≡ x
  ε-unit₁ [] = refl
  ε-unit₁ (x ∷ xs) = cong (_∷_ x) (ε-unit₁ xs)
  
  ε-unit₂ : ∀ {A} → (x : List A) → x ≡ (x ● [])
  ε-unit₂ [] = refl
  ε-unit₂ (x ∷ xs) = cong (_∷_ x) (ε-unit₂ xs)
  
  assoc-Monoid : ∀ {A} → (x y z : List A) → ((x ● y) ● z) ≡ (x ● (y ● z))
  assoc-Monoid [] ys zs = refl
  assoc-Monoid (x ∷ xs) ys zs = cong (_∷_ x) (assoc-Monoid xs ys zs)

map-++-commute : ∀ {A B} (f : A → B) xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute _ []       _  = refl
map-++-commute f (x ∷ xs) ys = cong (_∷_ (f x)) (map-++-commute f xs ys)

++-assoc : ∀ {K : Set} (a b c : List K) -> a ++ b ++ c ≡ (a ++ b) ++ c
++-assoc [] b c = refl
++-assoc (x ∷ a) b c = cong (_∷_ x) (++-assoc a b c)

concat-++-commute : {A : Set} (xs ys : List (List A)) →
                    concat (xs ++ ys) ≡ concat xs ++ concat ys
concat-++-commute []         _   = refl
concat-++-commute (xs ∷ xss) yss =
  begin
    xs ++ concat (xss ++ yss)
      ≡⟨ cong (_++_ xs) (concat-++-commute xss yss) ⟩
    xs ++ concat xss ++ concat yss
      ≡⟨ ++-assoc xs (concat xss) (concat yss) ⟩
    (xs ++ concat xss) ++ concat yss
  ∎
    where open Relation.Binary.PropositionalEquality.≡-Reasoning

applicativeList : Applicative List
applicativeList = mkApplicative pure _<*>_  pure-id <*>-∘ hom_law app_pure_law where
  open Functor {{...}}

  pure : ∀ {A} → A → List A
  pure x = x ∷ []

  _<*>_ : ∀ {A B} → List (A → B) → List A → List B
  [] <*> xs = []
  (f ∷ fs) <*> xs = map f xs ++ fs <*> xs

  pure-id : ∀ {A} → (fx : List A) → ((pure id) <*> fx) ≡ fx
  pure-id [] = refl
  pure-id (x ∷ xs) = cong (_∷_ x) (pure-id xs)

  <*>-∘ : ∀ {A B C} → (f : List (B → C))(g : List (A → B))(x : List A) → (((pure (λ f g → f ∘ g) <*> f) <*> g) <*> x) ≡ (f <*> (g <*> x))
  <*>-∘ [] g x = refl
  <*>-∘ (f ∷ fs) [] x = cong (map f) refl
  <*>-∘ (f ∷ fs) (g ∷ gs) xs = cong (map (f ∘ g)) refl
  
  hom_law : ∀ {A B}(f : A → B)(x : A) → (pure f <*> pure x) ≡ pure (f x)
  hom_law f x = refl

  app_pure_law : ∀ {A B}(f : List (A → B))(x : A) → (f <*> pure x) ≡ (pure (λ f → f $ x) <*> f)
  app_pure_law [] x = refl
  app_pure_law (f ∷ fs) x = cong (_∷_ (f x)) (app_pure_law fs x)

kleisliList : KleisliTriple List
kleisliList = mkKleisli return bind assoc-bind unity-left-bind unity-right-bind where
  open Functor {{...}}
  return : ∀ {A} → A → List A
  return x = x ∷ []

  bind : ∀ {A B} → (A → List B) → List A → List B
  bind f xs = concat (map f xs)

  _>>=_ : ∀ {A B} → List A → (A → List B) → List B
  _>>=_ = flip bind

  assoc-bind : ∀ {A B C} → (f : A → List B) → (g : B → List C) → (mx : List A) → ((mx >>= f) >>= g) ≡ (mx >>= ((bind g) ∘ f))
  assoc-bind f g [] = refl
  assoc-bind f g (x ∷ xs) =
    begin {!concat (map g (f x ++ concat (map f xs)))
          ≡⟨ cong concat (map-++-commute g (f x)
               (concat (map f xs))) ⟩
        concat (map g (f x) ++ map g (concat (map f xs)))
          ≡⟨ concat-++-commute (map g (f x))
               (map g (concat (map f xs))) ⟩
        concat (map g (f x)) ++ concat (map g (concat (map f xs)))
          ≡⟨ cong (_++_ (concat (map g (f x)))) (assoc-bind xs) ⟩
        concat (map g (f x)) ++ concat (map (bind g ∘ f) xs)
      ∎!}
    
        where open Relation.Binary.PropositionalEquality.≡-Reasoning

  unity-left-bind : ∀ {A B} → (f : A → List B) → (x : A) → (return x) >>= f ≡ f x
  unity-left-bind f x = cong (bind f) refl
  
  unity-right-bind : ∀ {A}(mx : List A) → bind return mx ≡ mx
  unity-right-bind [] = refl
  unity-right-bind (x ∷ x₁) = cong (_∷_ x) (unity-right-bind x₁)
