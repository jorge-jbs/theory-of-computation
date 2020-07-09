{-# OPTIONS --cubical #-}

module FA-Regex-Equiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic

open import Lang
open import DFA
open import NFA
open import NFA-e
open import Regex

module _ {A : Type₀} (IsA : IsAlphabet A) where
  DFA~Regex : DfaLangs IsA ≡ RegexLangs IsA
  DFA~Regex = {!!}

  DFA~NFA : DfaLangs IsA ≡ NfaLangs IsA
  DFA~NFA = {!!}

  DFA~NFA-ε : DfaLangs IsA ≡ NFAεLangs IsA
  DFA~NFA-ε = {!!}
