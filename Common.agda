{-# OPTIONS --cubical #-}

module Common where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level
    A : Type ℓ

it : {{_ : A}} → A
it {{x}} = x
