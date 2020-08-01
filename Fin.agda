{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Fin where

open import Agda.Builtin.Bool
import Agda.Builtin.Equality as Builtin
open import Cubical.Foundations.Prelude as Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Relation.Nullary using (Dec; Discrete; yes; no; mapDec)
open import Cubical.Relation.Nullary.DecidableEq using (Discrete→isSet)
import Cubical.Data.Fin as C
open import Cubical.Data.List hiding ([_])
import Cubical.Data.Empty as ⊥
import Data.Nat as S
import Data.Nat.Properties as S
open import Data.Fin as F hiding (_≤?_; _<?_)
open import Data.Fin using (Fin; zero; suc) public
open import Data.Fin.Properties as F hiding (_≤?_; _<?_)
import Data.Empty as Empty

open import Common

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
    A B : Type ℓ

isFinSet : Type ℓ → Type ℓ
isFinSet A = ∥ Σ ℕ (λ n → A ≃ Fin n) ∥

isProp-isFinSet : isProp (isFinSet A)
isProp-isFinSet = propTruncIsProp

FinSet : Type (ℓ-suc ℓ)
FinSet = TypeWithStr _ isFinSet

isFinSet→Discrete : {{_ : isFinSet A}} → Discrete A
isFinSet→Discrete = TODO

instance
  isFinSetFin : ∀ {n} → isFinSet (Fin n)
  isFinSetFin = ∣ _ , pathToEquiv refl ∣

isFinSet→isSet : {ℓ : Level} {A : Type ℓ} {{_ : isFinSet A}} → isSet A
isFinSet→isSet {A = A} =
  PT.elim
    (λ _ → isPropIsSet)
    (λ x → x)
    (∥isSetA∥ it)
  where
    ∥isSetA∥ : isFinSet A → ∥ isSet A ∥
    ∥isSetA∥ ∣ n , A≃Fin ∣ = ∣ transport (cong isSet LiftFin≡A) isSetLiftFin ∣
      where
        LiftFin≡A : Lift (Fin n) ≡ A
        LiftFin≡A =
          ua
            ( Lift (Fin n) ≃⟨ invEquiv LiftEquiv ⟩
              Fin n ≃⟨ invEquiv A≃Fin ⟩
              A ■
            )
        isSetLiftFin : isSet (Lift (Fin n))
        isSetLiftFin (Prelude.lift x) (Prelude.lift y) p q = p≡q
          where
            p′ q′ : x ≡ y
            p′ i = lower (p i)
            q′ i = lower (q i)
            p′≡q′ : p′ ≡ q′
            p′≡q′ = isSetFin _ _ _ _
            p≡q : p ≡ q
            p≡q i j = Prelude.lift (p′≡q′ i j)
    ∥isSetA∥ (squash x y i) = squash (∥isSetA∥ x) (∥isSetA∥ y) i

_≤?_ : ∀ x y → Dec (x S.≤ y)
zero ≤? y = yes S.z≤n
suc x ≤? zero = no (λ ())
suc x ≤? suc y = mapDec S.s≤s (λ { p (S.s≤s q) → p q }) (x ≤? y)

_<?_ : ∀ x y → Dec (x S.< y)
x <? y = suc x ≤? y

lower< : ∀ {n m} → (x : Fin (n ℕ.+ m)) → toℕ x S.< n → Fin n
lower< zero (S.s≤s le) = zero
lower< (suc x) (S.s≤s le) = suc (lower< x le)

equiv-⊎ : {n m : ℕ} {A B : Type ℓ} → A ≃ Fin n → B ≃ Fin m → A ⊎ B ≃ Fin (n ℕ.+ m)
equiv-⊎ {n = n} {m = m} {A = A} {B = B} p q =
  isoToEquiv (iso ⊎→Fin Fin→⊎ Fin→⊎→Fin ⊎→Fin→⊎)
  where
    f : A → Fin n
    f = Iso.fun (equivToIso p)
    f⁻¹ : Fin n → A
    f⁻¹ = Iso.inv (equivToIso p)
    g : B → Fin m
    g = Iso.fun (equivToIso q)
    g⁻¹ : Fin m → B
    g⁻¹ = Iso.inv (equivToIso q)
    ⊎→Fin : A ⊎ B → Fin (n ℕ.+ m)
    ⊎→Fin (⊎.inl a) = inject+ _ (f a)
    ⊎→Fin (⊎.inr b) =
      subst
        (λ h → Fin (h ℕ.+ m))
        (lemma _)
        (fromℕ n F.+ g b)
      where
        lemma : ∀ n → toℕ (fromℕ n) ≡ n
        lemma zero    = refl
        lemma (suc n) = cong suc (lemma n)

    lemma : ∀ n m → n S.≤ n ℕ.+ m
    lemma zero m = S.z≤n
    lemma (suc n) m = S.s≤s (lemma _ _)

    helper : ∀ {A : Type ℓ} {x y : A} → x Builtin.≡ y → x ≡ y
    helper Builtin.refl = refl

    helper₂ : ∀ {A : Type ℓ} {x y : A} → x ≡ y → x Builtin.≡ y
    helper₂ {x = x} p = J (λ y′ _ → x Builtin.≡ y′) Builtin.refl p

    Fin→⊎ : Fin (n ℕ.+ m) → A ⊎ B
    Fin→⊎ x with toℕ x <? n
    ... | yes le = ⊎.inl (f⁻¹ (lower< x le))
    ... | no ¬le = ⊎.inr (g⁻¹ (inject≤ y lemma₅))
      where
        x≥n : toℕ x S.≥ n
        x≥n = S.≮⇒≥ λ p → ⊥.elim (¬le p)

        lemma₃ : toℕ x ≡ toℕ x ∸ n ℕ.+ n
        lemma₃ =
          toℕ x ≡⟨ refl ⟩
          0 ℕ.+ toℕ x ≡⟨ helper (S.+-comm zero (toℕ x)) ⟩
          toℕ x ℕ.+ 0 ≡⟨ sym (cong (λ h → toℕ x ℕ.+ h) (helper (S.n∸n≡0 n))) ⟩
          toℕ x ℕ.+ (n ∸ n) ≡⟨ sym (helper (S.+-∸-assoc (toℕ x) {n = n} S.≤-refl)) ⟩
          toℕ x ℕ.+ n   ∸ n ≡⟨ helper (S.+-∸-comm n x≥n) ⟩
          toℕ x   ∸ n ℕ.+ n ∎

        lemma₄ : suc (toℕ x) S.≤ m ℕ.+ n
        lemma₄ =
          subst
            (suc (toℕ x) S.≤_)
            (helper (S.+-comm n m))
            (F.toℕ<n x)

        lemma₅ : suc (toℕ x ∸ n) S.≤ m
        lemma₅ =
          S.+-cancelʳ-≤
            {x = n}
            (suc (toℕ x ∸ n))
            m
            (subst
              (λ h → suc h S.≤ m S.+ n)
              lemma₃
              lemma₄
            )

        y : Fin (suc (toℕ x ∸ n))
        y = fromℕ (toℕ x ℕ.∸ n)
    Fin→⊎→Fin : ∀ x → ⊎→Fin (Fin→⊎ x) ≡ x
    Fin→⊎→Fin x with toℕ x <? n
    ... | yes le = {!!}
    ... | no ¬le =
      helper (F.toℕ-injective (helper₂ {!prf!}))
      where
        prf′ : toℕ (inject≤ (fromℕ (toℕ x ℕ.∸ n)) {!!}) ≡ toℕ x
        prf′ = {!!}
        prf :
          toℕ
            (subst
              (λ h → Fin (h S.+ m))
              {!!}
              (fromℕ n F.+
                Iso.fun (equivToIso q)
                (Iso.inv (equivToIso q)
                (inject≤ (fromℕ (toℕ x ℕ.∸ n)) {!!}))))
          ≡ toℕ x
        prf = subst
          (λ h → toℕ h ≡ toℕ x)
          (sym (isSet-subst {!!} {!!} {!!}))
          prf′
    ⊎→Fin→⊎ : ∀ x → Fin→⊎ (⊎→Fin x) ≡ x
    ⊎→Fin→⊎ = {!!}

instance
  isFinSet-⊎ : {{_ : isFinSet A}} {{_ : isFinSet B}} → isFinSet (A ⊎ B)
  isFinSet-⊎ = {!!}
