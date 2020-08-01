{-# OPTIONS --cubical #-}

module Axioms where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum

record LEM {ℓ : Level} : Type (ℓ-suc ℓ) where
  field
    decide : ∀ (P : Type ℓ) → isProp P → P ⊎ (¬ P)

classical-decide : ∀ {ℓ} {{lem : LEM {ℓ}}}  (P : Type ℓ) → isProp P → P ⊎ (¬ P)
classical-decide {{lem}} = lem .LEM.decide

private
  open import Cubical.Data.Nat
  open import Common
  example : {{lem : LEM}} → ℕ → ℕ
  example x with classical-decide (x ≡ 0) (isSetℕ x 0)
  ... | inl _ = x + 1
  ... | inr _ = x ∸ 1
