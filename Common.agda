{-# OPTIONS --cubical #-}

module Common where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level
    A : Type ℓ

it : {{_ : A}} → A
it {{x}} = x

infixr 0 _$_

_$_
  : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A → Type ℓ₂}
  → ((x : A) → B x)
  →  (x : A) → B x
f $ x = f x

_∋_ : ∀ {ℓ} (A : Type ℓ) → A → A
A ∋ t = t

postulate
  TODO : A
