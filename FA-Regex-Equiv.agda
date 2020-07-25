{-# OPTIONS --cubical #-}

module FA-Regex-Equiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic

open import Fin
open import Lang
open import DFA
open import NFA
open import NFA-e
open import Regex

module _ {A : Type₀} {{isFinSetA : isFinSet A}} where
  DFA~Regex : DfaLangs A ≡ RegexLangs A
  DFA~Regex = {!!}

  DFA~NFA : DfaLangs A ≡ NfaLangs A
  DFA~NFA = {!!}

  DFA~NFA-ε : DfaLangs A ≡ NFAεLangs A
  DFA~NFA-ε = {!!}
