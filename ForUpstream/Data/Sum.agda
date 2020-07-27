{-# OPTIONS --cubical --safe #-}

module ForUpstream.Data.Sum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit

private
  variable
    ℓ : Level
    A B C D : Type ℓ

inl≢inr : ∀ {x : A} {y : B} → ⊎.inl x ≡ ⊎.inr y → [ ⊥ ]
inl≢inr {A = A} {B = B} {x = x} {y = y} inl-eq-inr =
  elim {C = F} (λ _ → F-inl) (λ _ → F-inr) (⊎.inr y)
  where
    F : A ⊎ B → Type₀
    F (⊎.inl _) = [ ⊤ ]
    F (⊎.inr _) = [ ⊥ ]

    F-inl : F (⊎.inl x)
    F-inl = tt

    F-inr : F (⊎.inr y)
    F-inr = transport (cong F inl-eq-inr) F-inl
