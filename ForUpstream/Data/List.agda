{-# OPTIONS --cubical --safe #-}

module ForUpstream.Data.List where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Maybe

private
  variable
    ℓ : Level
    A B C D : Type ℓ

map : (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

head-maybe : List A → Maybe A
head-maybe [] = nothing
head-maybe (x ∷ _) = just x
