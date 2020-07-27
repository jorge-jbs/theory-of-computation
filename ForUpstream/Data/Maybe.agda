{-# OPTIONS --cubical --safe #-}

module ForUpstream.Data.Maybe where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Maybe

private
  variable
    ℓ : Level
    A B C D : Type ℓ

from-maybe : A → Maybe A → A
from-maybe default nothing = default
from-maybe default (just x) = x
