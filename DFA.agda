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

infixr 0 _$_

_$_
  : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A → Type ℓ₂}
  → ((x : A) → B x)
  →  (x : A) → B x
f $ x = f x

_∋_ : ∀ {ℓ} (A : Type ℓ) → A → A
A ∋ t = t

module _ (A : Type₀) {{isFinSetA : isFinSet A}} where
  record DFA : Type₁ where
    field
      Q : Type₀
      instance isFinSetQ : isFinSet Q
      δ : Q → A → Q
      initial-state : Q
      F : ℙ Q

    δ̂ : Q → Word A → Q
    δ̂ q [] = q
    δ̂ q (a ∷ w) = δ̂ (δ q a) w

    lang : Lang A
    lang w = F (δ̂ initial-state w)

  {-
  Languages definable by deterministic finite automata
  -}
  DfaLangs : ℙ (Lang A)
  DfaLangs N = ∃[ M ∶ DFA ] (DFA.lang M ≡ N) , powersets-are-sets _ _

module example-2-1 where
  δ : Fin 3 → Fin 2 → Fin 3
  δ zero zero = suc (suc zero)
  δ zero (suc zero) = zero
  δ (suc zero) a = suc zero
  δ (suc (suc zero)) zero = suc (suc zero)
  δ (suc (suc zero)) (suc zero) = suc zero

  A : Type₀
  A = Fin 2

  M : DFA A
  M = record
    { Q = Fin 3
    ; isFinSetQ = it
    ; δ = δ
    ; initial-state = zero
    ; F = λ q → (q ≡ suc zero) , isSetFin q (suc zero)
    }

  P : Word A → hProp ℓ-zero
  P [] = ⊥
  P (a ∷ []) = ⊥
  P (zero ∷ suc zero ∷ _) = ⊤
  P (zero ∷ zero ∷ w) = P (zero ∷ w)
  P (suc zero ∷ b ∷ w) = P (b ∷ w)

  δ̂ = DFA.δ̂ M
  L = DFA.lang M

  δ-1-idempotent : ∀ a → δ (suc zero) a ≡ suc zero
  δ-1-idempotent _ = refl

  δ̂-1-idempotent : ∀ w → δ̂ (suc zero) w ≡ suc zero
  δ̂-1-idempotent [] = refl
  δ̂-1-idempotent (x ∷ w) = δ̂-1-idempotent w

  δ̂-lemma- : ∀ w → DFA.δ̂ M (suc zero) w ≡ suc zero
  δ̂-lemma- [] = refl
  δ̂-lemma- (a ∷ w) = δ̂-lemma- w

  δ̂-lemma : ∀ q w → DFA.δ̂ M q (zero ∷ suc zero ∷ w) ≡ suc zero
  δ̂-lemma zero [] = refl
  δ̂-lemma (suc zero) [] = refl
  δ̂-lemma (suc (suc zero)) [] = refl
  δ̂-lemma zero (x ∷ w) = δ̂-lemma- w
  δ̂-lemma (suc zero) (x ∷ w) = δ̂-lemma- w
  δ̂-lemma (suc (suc zero)) (x ∷ w) = δ̂-lemma- w

  P⊆L : P ⊆ L
  P⊆L (zero ∷ zero ∷ w) p = P⊆L (zero ∷ w) p
  P⊆L (zero ∷ suc zero ∷ w) _ = δ̂-lemma zero w
  P⊆L (suc zero ∷ b ∷ w) p = P⊆L (b ∷ w) p

  ¬L-[] : [ ¬ (L []) ]
  ¬L-[] = znots-std

  ¬L-∷[] : ∀ a → [ ¬ (L (a ∷ [])) ]
  ¬L-∷[] zero = znots-std ∘ sym ∘ injSuc-std
  ¬L-∷[] (suc zero) = znots-std

  L-01 : ∀ w → [ L (zero ∷ suc zero ∷ w) ]
  L-01 w = lemma
    where
      lemma : δ̂ zero (zero ∷ suc zero ∷ w) ≡ suc zero
      lemma = δ̂-1-idempotent w

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
