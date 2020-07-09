{-# OPTIONS --cubical --allow-unsolved-metas #-}

module NFA-e where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Maybe

open import Lang
open import Fin

module _ {A : Type₀} (A-alph : IsAlphabet A) where
  record NFA-ε : Type₁ where
    field
      Q : Type₀
      Q-fin : IsFinite Q
      δ : Q → Maybe A → ℙ Q
      initial-state : Q
      F : ℙ Q

    is-path-of-εs : List Q → hProp _
    is-path-of-εs [] = ⊤
    is-path-of-εs (_ ∷ []) = ⊤
    is-path-of-εs (r ∷ s ∷ qs) = δ r nothing s ⊓ is-path-of-εs (s ∷ qs)

    closure : Q → ℙ Q
    closure q p = ∃[ qs ∶ List Q ] is-path-of-εs (q ∷ qs ++ p ∷ [])

    δ̂ : Q → Word A-alph → ℙ Q
    δ̂ q [] = closure q
    δ̂ q (a ∷ w) p = ∃[ r ∶ Q ] ∃[ s ∶ Q ] closure q r ⊓ δ r (just a) s ⊓ δ̂ s w p
      -- p ∈ δ̂ q (a ∷ w) iff (for some states r and s):
      --     there exists a path of the form q …—ε→… r —a→ s …—w→… p

    lang : Lang A-alph
    lang w = ∃[ p ∶ Q ] δ̂ initial-state w p ⊓ F p

  open NFA-ε

  {-
  Languages definable by non-deterministic finite automata with empty transitions
  -}
  NFAεLangs : ℙ (Lang A-alph)
  NFAεLangs N = ∃[ M ∶ NFA-ε ] (lang M ≡ N) , powersets-are-sets _ _
