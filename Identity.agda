module Identity where

data Identity (A : Set) : Set where
  identity : A → Identity A
