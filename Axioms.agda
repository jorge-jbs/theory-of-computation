{-# OPTIONS --cubical #-}

module Axioms where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum

record LEM : Typeω where
  field
    decide : ∀ {ℓ} (P : Type ℓ) → isProp P → P ⊎ (¬ P)

classical-decide : ∀ {{_ : LEM}} {ℓ} (P : Type ℓ) → isProp P → P ⊎ (¬ P)
classical-decide {{lem}} = lem .LEM.decide

private
  open import Cubical.Data.Nat
  open import Common
  example : {{_ : LEM}} → ℕ → ℕ
  example x with classical-decide (x ≡ 0) (isSetℕ x 0)
  ... | inl _ = x + 1
  ... | inr _ = x ∸ 1
