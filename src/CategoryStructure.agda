module CategoryStructure where

morAssoc : {A B C D : Set} → (f : A → B)(g : B → C)(h : C → D)(x : A) → (h ∘ (g ∘ f)) x ≡ ((h ∘ g) ∘ f) x
morAssoc f g h x = refl

idMor : {A B : Set} → (f : A → B)(x : A) → (id ∘ f) x ≡ (f ∘ id) x
idMor f x = refl

record Functor (F : Set → Set) : Set₁ where
  constructor mkFunctor
  infixl 4 _<$>_ _<$_ _$>_
  field
    fmap : {A B : Set} → (A → B) → F A → F B
    fmap-id : {A : Set}(fx : F A) → fmap id fx ≡ id fx
    fmap-∘ : {A B C : Set}(g : B → C)(f : A → B)(fx : F A) → fmap (g ∘ f) fx ≡ (fmap g ∘ fmap f) fx
  _<$>_ : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap
  _<$_ : ∀ {A B} → A → F B → F A
  _<$_ = fmap ∘ const
  _$>_ : ∀ {A B} → F A → B → F B
  _$>_ = flip (fmap ∘ const)
open Functor {{...}} public

record Applicative (F : Set → Set) : Set₁ where
  constructor mkApplicative
  infixl 2 _<*>_ _<**>_ _<*_ _*>_
  field
    pure : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    pure-id : ∀ {X} (x : F X) → (pure id <*> x) ≡ x
    pure-∘ : ∀ {R S T} (f : F (S → T))(g : F (R → S))(r : F R) → (pure (λ f g → f ∘ g) <*> f <*> g <*> r) ≡ (f <*> (g <*> r))
    pure-hom : ∀ {S T} (f : S → T)(s : S) → (pure f <*> pure s) ≡ (pure (f s))
    pure-inter : ∀ {S T} (f : F (S → T))(s : S) → (f <*> pure s) ≡ (pure (λ f → f s) <*> f)
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
  _<**>_ = flip _<*>_
  functor : Functor F
  functor = mkFunctor map map-id map-∘ where
    map : ∀ {A B} → (A → B) → F A → F B
    map f x = (pure f) <*> x

    map-id : {A : Set}(fx : F A) → map id fx ≡ id fx
    map-id = pure-id
    
    map-∘ : {A B C : Set}(g : B → C)(f : A → B)(fx : F A) → map (g ∘ f) fx ≡ (map g ∘ map f) fx
    map-∘ g f x = sym $ begin
      _<*>_ (pure g) (_<*>_ (pure f) x)
      ≡⟨ sym (pure-∘ (pure g) (pure f) x) ⟩
      _<*>_ (_<*>_ (_<*>_ (pure (λ f g → f ∘ g)) (pure g)) (pure f)) x
      ≡⟨ cong (λ fx → fx <*> pure f <*> x) (pure-hom (λ g f → g ∘ f) g) ⟩
      (_<*>_ (_<*>_ (pure (λ f → g ∘ f)) (pure f)) x)
      ≡⟨ cong (λ fx → fx <*> x) (pure-hom (λ f → g ∘ f) f) ⟩
      refl
open Applicative {{...}} public


_⇒_ : ∀ (F G : Set → Set) → Set₁
F ⇒ G = ∀ {X} → F X → G X
   

record Foldable (T : Set → Set) : Set₁ where
  constructor mkFoldable
  field
    foldr : ∀ {A B : Set} → (A → B → B) → B → T A → B 

record Monad (F : Set → Set) {{functor : Functor F}} : Set₁ where
  constructor mkMonad
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
  liftM : ∀ {A B} → (A → B) → F A → F B
  liftM f x = bind (λ x → return (f x)) x
  join : ∀ {A} → F (F A) → F A
  join f = f >>= id
                   
  
  
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
