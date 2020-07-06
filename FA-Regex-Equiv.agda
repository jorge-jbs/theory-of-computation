{-# OPTIONS --cubical #-}

module FA-Regex-Equiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic

open import Lang
open import DFA
open import Regex

module _ {A : Type₀} (IsA : IsAlphabet A) where
  DFA~Regex : DfaLangs IsA ≡ RegexLangs IsA
  DFA~Regex = {!!}
