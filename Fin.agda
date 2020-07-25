{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Fin where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation 
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (Discrete; yes; no; mapDec)
open import Cubical.Relation.Nullary.DecidableEq using (Discrete→isSet)
import Cubical.Data.Fin as C
open import Cubical.Data.List hiding ([_])
import Cubical.Data.Empty as ⊥
import Data.Nat as S
open import Data.Fin as S
open import Data.Fin using (Fin; zero; suc) public
import Data.Fin.Properties
import Data.Empty as Empty

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

isFinite→isSet : {A : Type₀} → IsFinite A → isSet A
isFinite→isSet (n , r) = transport (cong isSet (sym r)) isSetFin

private
  variable
    ℓ : Level
    A : Type ℓ

isFinSet : Type ℓ → Type ℓ
isFinSet A = ∥ Σ ℕ (λ n → A ≃ Fin n) ∥

isProp-isFinSet : isProp (isFinSet A)
isProp-isFinSet = propTruncIsProp

FinSet : Type (ℓ-suc ℓ)
FinSet = TypeWithStr _ isFinSet

-- Is this even true?
isFinSet→isSet : {{_ : isFinSet A}} → isSet A
isFinSet→isSet = {!!}

instance
  isFinSetFin : ∀ {n} → isFinSet (Fin n)
  isFinSetFin = ∣ _ , pathToEquiv refl ∣
