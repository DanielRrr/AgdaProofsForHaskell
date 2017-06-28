module CategoryStructure where

open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid; sym; trans; subst)
open import Identity
open Relation.Binary.PropositionalEquality.≡-Reasoning

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
  functor = mkFunctor fmap fmap-id fmap-∘ where
    fmap : ∀ {A B} → (A → B) → F A → F B
    fmap f x = (pure f) <*> x

    fmap-id : {A : Set}(fx : F A) → fmap id fx ≡ id fx
    fmap-id = pure-id
    
    fmap-∘ : {A B C : Set}(g : B → C)(f : A → B)(fx : F A) → fmap (g ∘ f) fx ≡ (fmap g ∘ fmap f) fx
    fmap-∘ g f x = sym $ begin
      _<*>_ (pure g) (_<*>_ (pure f) x)
      ≡⟨ sym (pure-∘ (pure g) (pure f) x) ⟩
      _<*>_ (_<*>_ (_<*>_ (pure (λ f g → f ∘ g)) (pure g)) (pure f)) x
      ≡⟨ cong (λ fx → fx <*> pure f <*> x) (pure-hom (λ g f → g ∘ f) g) ⟩
      (_<*>_ (_<*>_ (pure (λ f → g ∘ f)) (pure f)) x)
      ≡⟨ cong (λ fx → fx <*> x) (pure-hom (λ f → g ∘ f) f) ⟩
      refl


_⇒_ : ∀ (F G : Set → Set) → Set₁
F ⇒ G = ∀ {X} → F X → G X
   

record Foldable (T : Set → Set) : Set₁ where
  constructor mkFoldable
  field
    foldr : ∀ {A B : Set} → (A → B → B) → B → T A → B 

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
  liftM : ∀ {A B} → (A → B) → F A → F B
  liftM f x = bind (λ x → return (f x)) x
  join : ∀ {A} → F (F A) → F A
  join f = f >>= id

  liftM-id : {A : Set}(fx : F A) → liftM id fx ≡ id fx
  liftM-id x = begin ((liftM id x) ≡⟨ unity-right-bind x ⟩ refl)

  unity-left : ∀ {A}(mx : F A) → join (return mx) ≡ mx
  unity-left mx =
                (join (return mx)) ≡⟨ refl ⟩
                ((bind id (return mx)) ≡⟨ (unity-left-bind id mx) ⟩ refl)
  
  unity-right : ∀ {A}(mx : F A) → join (liftM return mx) ≡ mx
  unity-right mx = join (liftM return mx)
                   ≡⟨ {!!} ⟩
                   {!!}
  
  naturality-return : ∀ {A B} (f : A → F B)(x : A) → return (f x) ≡ liftM f (return x)
  naturality-return f x = sym $ begin
                      (liftM f (return x)) ≡⟨ (unity-left-bind (λ a → return (f a)) x) ⟩
                      refl

  naturality-join : ∀ {A B}(f : A → F B)(mmx : F ( F A )) → join (liftM (liftM f) mmx) ≡ liftM f (join mmx)
  naturality-join f mx = {!!}


  
  appF : Applicative F
  appF = mkApplicative pure _<*>_ pure-id pure-∘ pure-hom pure-inter where
    pure : ∀ {A} → A → F A
    pure = return
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    _<*>_ fm x = fm >>= (λ f → x >>= λ s → return (f s) )
    
    pure-id : ∀ {X} (x : F X) → (pure id <*> x) ≡ x
    pure-id x = begin
            ((pure id <*> x)
            ≡⟨ unity-left-bind (λ f → bind (λ y → return (f y)) x) id ⟩
            (bind (λ y → return (id y)) x)
            ≡⟨ unity-right-bind x ⟩
            refl)

    pure-hom : ∀ {S T} (f : S → T)(s : S) → (pure f <*> pure s) ≡ (pure (f s))
    pure-hom f s = begin
                 ((pure f <*> pure s)
                 ≡⟨ unity-left-bind (λ f → bind (λ x → return (f x)) (return s)) f ⟩
                 bind (λ x → return (f x)) (return s)
                 ≡⟨ unity-left-bind (λ x → return (f x)) s ⟩
                 refl)
                 
    pure-inter : ∀ {S T} (f : F (S → T))(s : S) → (f <*> pure s) ≡ (pure (λ f → f s) <*> f)
    pure-inter f s = sym $ begin
                     ((pure (λ f → f s) <*> f)
                     ≡⟨ refl ⟩
                     bind (λ a → bind (λ b → return (a b)) f) (return (λ f → f s))
                     ≡⟨ unity-left-bind (λ a → bind (λ b → return (a b)) f) (λ f → f s) ⟩
                     bind (λ b → return (b s)) f
                     ≡⟨ refl ⟩
                     liftM (λ f → f s) f ≡⟨ refl ⟩
                     (sym $ begin
                     (f <*> (return s))
                     ≡⟨ {!!} ⟩ {!!}))
    
    pure-∘ : ∀ {R S T} (f : F (S → T))(g : F (R → S))(r : F R) → (((pure (λ f g → f ∘ g) <*> f) <*> g) <*> r) ≡ (f <*> (g <*> r))
    pure-∘ f g r = {!!}
                   
  
  
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
