{-# OPTIONS --cubical --allow-unsolved-metas #-}

module NFA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Function
open import Cubical.Data.List hiding ([_])

open import Common
open import Lang
open import Fin

module _ (A : Type₀) {{isFinSetA : isFinSet A}} where
  record NFA : Type₁ where
    field
      Q : Type₀
      instance Q-fin : isFinSet Q
      δ : Q → A → ℙ Q
      initial-state : Q
      F : ℙ Q

    δ̂ : Q → Word A → ℙ Q
    δ̂ q [] p = (p ≡ q) , isFinSet→isSet _ _
    δ̂ q (a ∷ w) p = ∃[ r ∶ Q ] δ q a r ⊓ δ̂ r w p

    lang : Lang A
    --lang w = F ∩ δ̂ initial-state w ≢ ∅
    lang w = ∃[ p ∶ Q ] δ̂ initial-state w p ⊓ F p

  open NFA

  {-
  Languages definable by non-deterministic finite automata
  -}
  NfaLangs : ℙ (Lang A)
  NfaLangs N = ∃[ M ∶ NFA ] (lang M ≡ N) , powersets-are-sets _ _

module example-2-6 where
  A : Type₀
  A = Fin 2

  Q = Fin 3

  δ : Q → A → ℙ Q
  δ zero zero q = ((q ≡ zero) , isSetFin _ _)  ⊓ ((q ≡ suc zero) , isSetFin _ _)
  δ zero (suc zero) q = (q ≡ zero) , isSetFin _ _
  δ (suc zero) zero q = ∅ q
  δ (suc zero) (suc zero) q = (q ≡ suc (suc zero)) , isSetFin _ _
  δ (suc (suc zero)) _ q = ∅ q

  M : NFA A
  M = record
    { Q = Q
    ; Q-fin = it
    ; δ = δ
    ; initial-state = zero
    ; F = λ p → (suc (suc zero) ≡ p) , isSetFin _ _
    }

  δ̂ = NFA.δ̂ M
  L = NFA.lang M

  P : Word A → hProp ℓ-zero
  P [] = ⊥
  P (a ∷ []) = ⊥
  P (zero ∷ suc zero ∷ _) = ⊤
  P (zero ∷ zero ∷ w) = P (zero ∷ w)
  P (suc zero ∷ b ∷ w) = P (b ∷ w)

  _ : L ≡ P
  _ = {!!}
