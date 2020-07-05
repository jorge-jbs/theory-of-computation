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

open import Lang

infixr 0 _$_

_$_
  : ∀ {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} {B : A → Type ℓ₂}
  → ((x : A) → B x)
  →  (x : A) → B x
f $ x = f x

_∋_ : ∀ {ℓ} (A : Type ℓ) → A → A
A ∋ t = t

znots-std : ∀ {m} {n : Fin m} → zero ≡ suc n → [ ⊥ ]
znots-std {m} {n} p = subst F p tt
  where
    F : Fin (suc m) → Type₀
    F zero = [ ⊤ ]
    F (suc _) = [ ⊥ ]

--zznotss-std : ∀ {m} {n : Fin m} → zero ≡ suc n → [ ⊥ ]

injSuc-std
  : ∀ {k} {m n : Fin k}
  → suc m ≡ suc n
  → m ≡ n
injSuc-std {k} {m} p = cong pred′ p
  where
    pred′ : Fin (suc k) → Fin k
    pred′ zero = m
    pred′ (suc q) = q

injSuc-std₂
  : ∀ {k} {m n : Fin k}
  → (m ≡ n → [ ⊥ ])
  → suc m ≡ suc n
  → [ ⊥ ]
injSuc-std₂ f p = f (injSuc-std p)

discreteFin : ∀ {n} → Discrete (Fin n)
discreteFin zero zero = yes refl
discreteFin (suc x) zero = no (znots-std ∘ sym)
discreteFin zero (suc y) = no znots-std
discreteFin (suc x) (suc y) = mapDec (cong suc) injSuc-std₂ (discreteFin x y)

isSetFin : ∀ {n} → isSet (Fin n)
isSetFin = Discrete→isSet discreteFin

IsFinite : Type₀ → Type₁
IsFinite A = Σ ℕ (λ n → A ≡ Fin n)

record DFA : Type₁ where
  field
    Q : Type₀
    Q-fin : IsFinite Q
    A : Type₀
    A-alph : IsAlphabet A
    δ : Q → A → Q
    initial-state : Q
    F : ℙ Q

  δ̂ : Q → Word A-alph → Q
  δ̂ q [] = q
  δ̂ q (a ∷ w) = δ̂ (δ q a) w

  L : Lang A-alph
  L w = F (δ̂ initial-state w)

module example-2-1 where
  δ : Fin 3 → Fin 2 → Fin 3
  δ zero zero = suc (suc zero)
  δ zero (suc zero) = zero
  δ (suc zero) a = suc zero
  δ (suc (suc zero)) zero = suc (suc zero)
  δ (suc (suc zero)) (suc zero) = suc zero

  M : DFA
  M = record
    { Q = Fin 3
    ; Q-fin = 3 , refl
    ; A = Fin 2
    ; A-alph = 2 , refl
    ; δ = δ
    ; initial-state = zero
    ; F = λ q → (q ≡ suc zero) , isSetFin q (suc zero)
    }

  P : Word (M .DFA.A-alph) → hProp ℓ-zero
  P [] = ⊥
  P (a ∷ []) = ⊥
  P (zero ∷ suc zero ∷ _) = ⊤
  P (zero ∷ zero ∷ w) = P (zero ∷ w)
  P (suc zero ∷ b ∷ w) = P (b ∷ w)

  δ̂ = DFA.δ̂ M
  L = DFA.L M

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
