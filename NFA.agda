{-# OPTIONS --cubical --allow-unsolved-metas #-}

module NFA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Function
open import Cubical.Data.List hiding ([_])

open import Lang
open import Fin

module _ {A : Type₀} (A-alph : IsAlphabet A) where
  record NFA : Type₁ where
    field
      Q : Type₀
      Q-fin : IsFinite Q
      δ : Q → A → ℙ Q
      initial-state : Q
      F : ℙ Q

    δ̂ : Q → Word A-alph → ℙ Q
    δ̂ q [] p = (p ≡ q) , isFinite→isSet Q-fin _ _
    δ̂ q (a ∷ w) p = ∃[ r ∶ Q ] δ q a r ⊓ δ̂ r w p

    L : Lang A-alph
    --L w = F ∩ δ̂ initial-state w) ≢ ∅
    L w = ∃[ p ∶ Q ] δ̂ initial-state w p ⊓ F p

  {-
  Languages definable by non-deterministic finite automata
  -}
  NfaLangs : ℙ (Lang A-alph)
  NfaLangs N = ∃[ M ∶ NFA ] (NFA.L M ≡ N) , powersets-are-sets _ _

module example-2-6 where
  A : Type₀
  A = Fin 2

  A-alph : IsAlphabet A
  A-alph = 2 , refl

  Q = Fin 3
  Q-fin : IsFinite Q
  Q-fin = 3 , refl

  δ : Q → A → ℙ Q
  δ zero zero q = ((q ≡ zero) , isSetFin _ _)  ⊓ ((q ≡ suc zero) , isSetFin _ _)
  δ zero (suc zero) q = (q ≡ zero) , isSetFin _ _
  δ (suc zero) zero q = ∅ q
  δ (suc zero) (suc zero) q = (q ≡ suc (suc zero)) , isSetFin _ _
  δ (suc (suc zero)) _ q = ∅ q

  M : NFA A-alph
  M = record
    { Q = Q
    ; Q-fin = Q-fin
    ; δ = δ
    ; initial-state = zero
    ; F = λ p → (suc (suc zero) ≡ p) , isSetFin _ _
    }

  δ̂ = NFA.δ̂ M
  L = NFA.L M

  P : Word A-alph → hProp ℓ-zero
  P [] = ⊥
  P (a ∷ []) = ⊥
  P (zero ∷ suc zero ∷ _) = ⊤
  P (zero ∷ zero ∷ w) = P (zero ∷ w)
  P (suc zero ∷ b ∷ w) = P (b ∷ w)

  _ : L ≡ P
  _ = {!!}
