{-# OPTIONS --rewriting -v rewriting:80 #-}
{-# OPTIONS --rewriting #-}
module Haskell_course where

open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Integer

postulate
  undefined : ∀ {a}{A : Set a} → A

id : ∀ {α}{A : Set α} → A → A
id x = x

const : ∀ {A B : Set} → A → B → A
const x y = x

const' : ∀ {A B : Set} → A → B → B
const' = const id

_∘_ : ∀ {α β γ} →
      {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ} →
      (f : {x : A} → (y : B x) → C y) →
      (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

infix 4 _≡_
data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN REWRITE _≡_ #-}

postulate
  A : Set
  f : A → A
  h : .A → A → A
  rew : ∀ {x} → h x x ≡ x
{-# REWRITE rew #-}

cong : {A B : Set}{a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

subst : {A : Set}{P : A → Set}{x y : A} → (x ≡ y) → P x → P y
subst refl A = A

sym : {A : Set}{a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

_$_ : ∀ {A B : Set} → (A → B) → A → B
f $ x = f x

postulate
  inj : ∀ {A B : Set}{a b : A}(f : A → A) → f a ≡ f b → a ≡ b


record EndoFunctor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
open EndoFunctor {{...}} public

record EndoFunctorOKP F {{FF : EndoFunctor F}} : Set₁ where
  field
    endoFunctorId : ∀ {X}(x : F X) → fmap {{FF}}{X} id x ≡ x
    endoFunctorCo : ∀ {R S T}(x : F R) → (f : S → T)(g : R → S) → (fmap {{FF}} f ∘ fmap g) x ≡ fmap (f ∘ g) x
open EndoFunctorOKP {{...}} public

record Category (cat : Set → Set → Set) : Set₁ where
  field
    identity : ∀ {A} → (cat A A)
    _>>_ : ∀ {A B C} → cat A B → cat B C → cat A C
open Category {{...}} public

record Kleisli (M : Set → Set) : Set₁ where
  field
    idK  : ∀ {A} → A → M A
    _>>_ : ∀ {A B C} → (A → M B) → (B → M C) → A → M C
open Kleisli {{...}} public

record Applicative (F : Set → Set) : Set₁ where
  infixl 2 _<*>_
  field
    pure : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record {fmap = _<*>_ ∘ pure}
open Applicative {{...}} public

record Monad (F : Set → Set) : Set₁ where
  field
    return : ∀ {A} → A → F A
    _>>=_  : ∀ {A B} → F A → (A → F B) → F B
  monadApplicative : Applicative F
  monadApplicative = record
    {pure  = return
    ;_<*>_ = λ ff fs → ff >>= λ f → fs >>= λ s → return (f s)
    }
open Monad {{...}} public



-- About 3D

data Point3D (A : Set) : Set where
  point3D : (x : A) → (y : A) → (z : A) → Point3D A

third_map : ∀ {A B} → (A → B) → Point3D A → Point3D B
third f map (point3D x y z) = point3D ((f x)) (f y) (f z)

Point3DEndo : EndoFunctor Point3D
Point3DEndo = record {fmap = third_map}

thirdPure : ∀ {A} → A → Point3D A
thirdPure x = point3D x x x

thirdApp : ∀ {A B} → Point3D (A → B) → Point3D A → Point3D B
thirdApp (point3D f g h) (point3D x y z) = point3D (f x) (g y) (h z)

thirdApplicative : Applicative Point3D
thirdApplicative = record {pure = thirdPure ; _<*>_ = thirdApp}

-- about GeomPrimitive

data GeomPrimitive (A : Set) : Set where
  Point : Point3D A → GeomPrimitive A
  LineSegment : Point3D A → Point3D A → GeomPrimitive A

geo_map : ∀ {A B} → (A → B) → GeomPrimitive A → GeomPrimitive B
geo_map f (Point x) = Point (third_map f x)
geo_map f (LineSegment x x₁) = LineSegment (third_map f x) (third_map f x₁)

GeoPrEndo : EndoFunctor GeomPrimitive
GeoPrEndo = record {fmap = geo_map}

-- Trees

data Tree (A : Set) : Set where
  Leaf : Tree A
  Branch : Tree A → A → Tree A → Tree A

TreeMap : ∀ {A B} → (A → B) → Tree A → Tree B
TreeMap f Leaf = Leaf
TreeMap f (Branch l x r) = Branch (TreeMap f l)(f x) (TreeMap f r)

EndoTree : EndoFunctor Tree
EndoTree = record {fmap = TreeMap}

pureTree : ∀ {A} → A → Tree A
pureTree x = Leaf

appTree : ∀ {A B} → Tree (A → B) → Tree A → Tree B
appTree Leaf x = Leaf
appTree (Branch f₁ x f₂) Leaf = Leaf
appTree (Branch f₁ x f₂) (Branch x₁ x₂ x₃) = Branch (appTree f₁ x₁) (x x₂) (appTree f₂ x₃)

idFact1 : ∀ {A}{x : A} → id x ≡ x
idFact1 = refl

postulate id-fact : ∀ {A}(x : Tree A) → TreeMap id x ≡ x

1stLawEndoTree : ∀ {A} → (TreeMap {A} $ id) ≡ id 
1stLawEndoTree = cong id {!!}

2ndLawEndoTree : ∀ {A B C}(x : Tree A) → (f : B → C)(g : A → B) → ((TreeMap f) ∘ (TreeMap g)) x ≡ TreeMap (f ∘ g) x
2ndLawEndoTree Leaf f g = refl
2ndLawEndoTree (Branch x x₁ x₂) f g =  {!!}

AppTree : Applicative Tree
AppTree = record { pure = pureTree ; _<*>_ = appTree }


-- Maybe
data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

maybeMap : ∀ {A B} → (A → B) → Maybe A → Maybe B
maybeMap f Nothing = Nothing
maybeMap f (Just x) = Just (f x)

maybe1stEndo : ∀ {A}(x : Maybe A) → (maybeMap id x) ≡ id x
maybe1stEndo Nothing = refl
maybe1stEndo (Just x) = refl

maybe2ndEndo : ∀ {A B C}(x : Maybe A) → (f : B → C)(g : A → B) → (maybeMap f ∘ maybeMap g) x ≡ maybeMap (f ∘ g) x
maybe2ndEndo Nothing f₁ g = refl
maybe2ndEndo (Just x) f₁ g = refl

justUnfold : {A : Set} → Maybe A → A
justUnfold (Just x) = x
justUnfold Nothing = undefined

maybeK : {A : Set } → {B : Set} → {C : Set} → (A → Maybe B) → (B → Maybe C) → A → Maybe C
maybeK f g x = g (justUnfold (f x))

maybeApp : ∀ {A B} → Maybe (A → B) → Maybe A → Maybe B
maybeApp Nothing x = Nothing
maybeApp (Just f) Nothing = Nothing
maybeApp (Just f) (Just x) = Just (f x)

maybeBind : ∀ {A B} → Maybe A → (A → Maybe B) → Maybe B
maybeBind Nothing f = Nothing
maybeBind (Just x) f = f x

maybeApplicative : Applicative Maybe
maybeApplicative = record {pure = Just ; _<*>_ = maybeApp}

maybeMonad : Monad Maybe
maybeMonad = record {return = Just ; _>>=_ = maybeBind}

-- Lists

EndoList : EndoFunctor List
EndoList = record {fmap = map}

listBind : ∀ {A : Set} → {B : Set} → List A → (A → List B) → List B
listBind [] f = []
listBind (x ∷ xs) f = (f x) ++ (listBind xs f)

listReturn : {A : Set} → A → List A
listReturn x = x ∷ []

listApp : ∀ {A B : Set} → List (A → B) → List A → List B
listApp [] x = []
listApp (x ∷ f) [] = []
listApp (x ∷ f) (x₁ ∷ x₂) = (x x₁) ∷ listApp f x₂

listApplicative : Applicative List
listApplicative = record {pure = listReturn ; _<*>_ = listApp}

listMonad : Monad List
listMonad =  record { return = listReturn ; _>>=_ = listBind }

IdLemma : ∀ {A : Set}(x : A)(xs : List A) → map id (x ∷ xs) ≡ (id x) ∷ map id xs
IdLemma x [] = refl
IdLemma x (x₁ ∷ xs) = sym (cong id refl)

postulate idFact2 : ∀ {A}(x x₁ : A)(xs : List A) → id x ∷ map id (x₁ ∷ xs) ≡ x ∷ x₁ ∷ xs

IdLemma₁ : ∀ {A : Set}(x : A)(xs : List A) → (id x) ∷ (map id xs) ≡ id (x ∷ xs)
IdLemma₁ x [] = refl
IdLemma₁ x (x₁ ∷ xs) = cong id (idFact2 x x₁ xs)

1stLawFunctorList : ∀ {A : Set}(x : List A) → map id x ≡ id x
1stLawFunctorList [] = refl
1stLawFunctorList (x ∷ x₁) = trans (IdLemma x x₁) (IdLemma₁ x x₁)

postulate composeFact₁ : {A B C : Set}(x : List A) → (f : B → C)(g : A → B) → ((map f) ∘ (map g)) x ≡ map f (map g x)

postulate composeFact₂ : {A B C : Set}(x : List A) → (f : B → C)(g : A → B) → map f (map g x) ≡ map (f ∘ g) x

2ndFunctorLawList : {A B C : Set}(x : List A) → (f : B → C)(g : A → B) → ((map f) ∘ (map g)) x ≡ map (f ∘ g) x
2ndFunctorLawList [] f₁ g = refl
2ndFunctorLawList (x ∷ x₁) f₁ g = trans (composeFact₁ (x ∷ x₁) f₁ g) (composeFact₂ (x ∷ x₁) f₁ g)
