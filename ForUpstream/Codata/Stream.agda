{-# OPTIONS --cubical #-}

module ForUpstream.Codata.Stream where

open import Cubical.Foundations.Prelude
open import Cubical.Codata.Stream
open Stream
open import Cubical.Data.List

private
  variable
    ℓ : Level
    A B C D : Type ℓ

_∷ₛ_ : A → Stream A → Stream A
head (x ∷ₛ xs) = x
tail (x ∷ₛ xs) = xs

repeat : A → Stream A
head (repeat x) = x
tail (repeat x) = repeat x

from-list : A → List A → Stream A
from-list z [] = repeat z
from-list z (x ∷ xs) = x ∷ₛ from-list z xs

data Suffix {A : Type₀} : Stream A → Stream A → Type₀ where
  here : ∀ {xs} → Suffix xs xs
  there : ∀ {xs y ys} → Suffix xs ys → Suffix xs (y , ys)
