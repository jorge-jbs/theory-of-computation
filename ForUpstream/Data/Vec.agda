{-# OPTIONS --cubical --safe #-}

module ForUpstream.Data.Vec where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level
    A B C : Type ℓ

map₂ : ∀ {k} → (A → B → C) → Vec A k → Vec B k → Vec C k
map₂ f [] [] = []
map₂ f (x ∷ xs) (y ∷ ys) = f x y ∷ map₂ f xs ys

repeat : ∀ {k} → A → Vec A k
repeat {k = zero} x = []
repeat {k = suc k} x = x ∷ repeat x

zip : ∀ {k} → Vec A k → Vec B k → Vec (A × B) k
zip [] [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys
