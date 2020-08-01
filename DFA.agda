{-# OPTIONS --cubical #-}

module DFA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Function
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Relation.Nullary using (Discrete; yes; no; mapDec)
open import Cubical.Relation.Nullary.DecidableEq using (Discrete→isSet)
import Cubical.Data.Fin as C
open import Cubical.Data.List hiding ([_])
import Cubical.Data.Empty as ⊥
import Data.Nat as S
open import Data.Fin as S
import Data.Fin.Properties
import Data.Empty as Empty

open import Common
open import Lang
open import Fin

module _ (Symbol : Type₀) {{isFinSetA : isFinSet Symbol}} where
  record DFA : Type₁ where
    field
      State : Type₀
      {{isFinSetState}} : isFinSet State
      next : State → Symbol → State
      start-state : State
      FinalState : ℙ State
      -- Maybe using Listed finite sets is a better idea, but they aren't very
      -- mature yet.
      --final-states : LFSet State

    run : State → Word Symbol → State
    run  q [] = q
    run q (a ∷ w) = run (next q a) w

    lang : Lang Symbol
    --lang w = run start-state w ∈ final-states
    lang w = FinalState (run start-state w)

  {-
  Languages definable by deterministic finite automata
  -}
  DfaLangs : ℙ (Lang Symbol)
  DfaLangs N = ∃[ M ∶ DFA ] (DFA.lang M ≡ N) , powersets-are-sets _ _

module example-2-1 where
  next : Fin 3 → Fin 2 → Fin 3
  next zero zero = suc (suc zero)
  next zero (suc zero) = zero
  next (suc zero) a = suc zero
  next (suc (suc zero)) zero = suc (suc zero)
  next (suc (suc zero)) (suc zero) = suc zero

  Symbol : Type₀
  Symbol = Fin 2

  M : DFA Symbol
  M = record
    { State = Fin 3
    ; isFinSetState = it
    ; next = next
    ; start-state = zero
    -- ; final-states = suc zero LFS.∷ LFS.[]
    ; FinalState = λ q → (q ≡ suc zero) , isSetFin q (suc zero)
    }

  P : Word Symbol → hProp ℓ-zero
  P [] = ⊥
  P (a ∷ []) = ⊥
  P (zero ∷ suc zero ∷ _) = ⊤
  P (zero ∷ zero ∷ w) = P (zero ∷ w)
  P (suc zero ∷ b ∷ w) = P (b ∷ w)

  run = DFA.run M
  L = DFA.lang M

  next-1-idempotent : ∀ a → next (suc zero) a ≡ suc zero
  next-1-idempotent _ = refl

  run-1-idempotent : ∀ w → run (suc zero) w ≡ suc zero
  run-1-idempotent [] = refl
  run-1-idempotent (x ∷ w) = run-1-idempotent w

  run-lemma- : ∀ w → DFA.run M (suc zero) w ≡ suc zero
  run-lemma- [] = refl
  run-lemma- (a ∷ w) = run-lemma- w

  run-lemma : ∀ q w → DFA.run M q (zero ∷ suc zero ∷ w) ≡ suc zero
  run-lemma zero [] = refl
  run-lemma (suc zero) [] = refl
  run-lemma (suc (suc zero)) [] = refl
  run-lemma zero (x ∷ w) = run-lemma- w
  run-lemma (suc zero) (x ∷ w) = run-lemma- w
  run-lemma (suc (suc zero)) (x ∷ w) = run-lemma- w

  P⊆L : P ⊆ L
  P⊆L (zero ∷ zero ∷ w) p = P⊆L (zero ∷ w) p
  P⊆L (zero ∷ suc zero ∷ w) _ = run-lemma zero w
  P⊆L (suc zero ∷ b ∷ w) p = P⊆L (b ∷ w) p

  ¬L-[] : [ ¬ (L []) ]
  ¬L-[] = znots-std

  ¬L-∷[] : ∀ a → [ ¬ (L (a ∷ [])) ]
  ¬L-∷[] zero = znots-std ∘ sym ∘ injSuc-std
  ¬L-∷[] (suc zero) = znots-std

  L-01 : ∀ w → [ L (zero ∷ suc zero ∷ w) ]
  L-01 w = lemma
    where
      lemma : run zero (zero ∷ suc zero ∷ w) ≡ suc zero
      lemma = run-1-idempotent w

  L-ind₁ : ∀ w → [ L (zero ∷ zero ∷ w)] → [ L (zero ∷ w)]
  L-ind₁ [] prf = ⊥.rec $ znots-std $ sym $ injSuc-std prf
  L-ind₁ (zero ∷ w) prf = L-ind₁ w prf
  L-ind₁ (suc zero ∷ w) prf = L-01 w

  L-ind₂ : ∀ w → [ L (suc zero ∷ zero ∷ w)] → [ L (zero ∷ w)]
  L-ind₂ [] prf = ⊥.rec $ znots-std $ sym $ injSuc-std prf
  L-ind₂ (zero ∷ w) prf = L-ind₁ w prf
  L-ind₂ (suc zero ∷ w) prf = L-01 w

  L-ind₃ : ∀ w → [ L (suc zero ∷ suc zero ∷ w)] → [ L (suc zero ∷ w)]
  L-ind₃ [] prf = ⊥.rec $ znots-std prf
  L-ind₃ (zero ∷ w) prf = L-ind₂ w prf
  L-ind₃ (suc zero ∷ w) prf = L-ind₃ w prf

  L-ind₄ : ∀ w b → [ L (suc zero ∷ b ∷ w)] → [ L (b ∷ w)]
  L-ind₄ w zero = L-ind₂ w
  L-ind₄ w (suc zero) = L-ind₃ w

  L⊆P : L ⊆ P
  L⊆P [] l = ¬L-[] l
  L⊆P (_ ∷ []) l = ¬L-∷[] _ l
  L⊆P (zero     ∷ zero     ∷ w) l = L⊆P (zero ∷ w) (L-ind₁ w l)
  L⊆P (zero     ∷ suc zero ∷ w) l = tt
  L⊆P (suc zero ∷ b        ∷ w) l = L⊆P (b ∷ w) (L-ind₄ w b l)

  _ : L ≡ P
  _ = ⊆-extensionality L P (L⊆P , P⊆L)
