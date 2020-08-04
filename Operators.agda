{-# OPTIONS --cubical #-}

module Operators where

open import Cubical.Foundations.Prelude

open import Common

private
  variable
    ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Level

record Has-× (A : Type ℓ₁) (B : Type ℓ₂) (C : Type ℓ₃)
    : Type (ℓ-max ℓ₁ (ℓ-max ℓ₂ ℓ₃)) where
  infixr 5 _×_
  field
    _×_ : A → B → C

open Has-× {{...}} public

instance
  Has-×-Type : Has-× (Type ℓ) (Type ℓ) (Type ℓ)
  Has-×-Type = record { _×_ = Sigma._×_ }
    where
      import Cubical.Data.Sigma as Sigma

record Has-⊕ (A : Type ℓ₁) (B : Type ℓ₂) (C : Type ℓ₃)
    : Type (ℓ-max ℓ₁ (ℓ-max ℓ₂ ℓ₃)) where
  field
    _⊕_ : A → B → C

open Has-⊕ {{...}} public

record Has-ᶜ (A : Type ℓ₁) (B : Type ℓ₂)
    : Type (ℓ-max ℓ₁ ℓ₂) where
  infix 6 _ᶜ
  field
    _ᶜ : A → B

open Has-ᶜ {{...}} public
