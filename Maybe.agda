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
