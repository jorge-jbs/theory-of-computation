{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Logic
open import Cubical.Data.Nat
--open import Cubical.Data.Fin
open import Cubical.Data.List
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Empty renaming (⊥ to Empty)

module Lang where

open import Fin

Finite : {X : Type ℓ-zero} → ℙ X → Type (ℓ-suc ℓ-zero)
Finite {X} A = Σ X (_∈ A) ≡ Σ ℕ Fin

FiniteSubset : Type₀ → Type₁
FiniteSubset X = Σ (ℙ X) Finite

data FSSet (A : Type₀) : Type₁ where
  [] : FSSet A
  _∷_ : (x : A) → (xs : FSSet A) → FSSet A
  comm : ∀ x y xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
  dedup : ∀ x xs → x ∷ x ∷ xs ≡ x ∷ xs
  trunc : isSet (FSSet A)

IsAlphabet : Type₀ → Type₁
IsAlphabet A = Σ ℕ (λ n → A ≡ Fin n)

module _ {ℓ}{X : Type ℓ} where
  ∅ : ℙ X
  ∅ _ = Lift Empty , λ ()

  infix 10 ⋃

  -- | Infinitary union. Borrowed from the standard library
  ⋃ : (I : Type₀) → (I → ℙ X) → ℙ X
  ⋃ I A x = ∃[ i ] A i x

  _∪_ : ℙ X → ℙ X → ℙ X
  (A ∪ B) x = A x ⊔ B x

  ∪-comm : (P Q : ℙ X) → P ∪ Q ≡ Q ∪ P
  ∪-comm P Q i x = ⊔-comm (P x) (Q x) i

  _∩_ : ℙ X → ℙ X → ℙ X
  (A ∩ B) x = A x ⊓ B x

module _ {A : Type₀} (IsA : IsAlphabet A) where
  IsAlphabet→IsSet : isSet A
  IsAlphabet→IsSet = transport (cong isSet (sym (IsA .snd))) isSetFin

  Word : Type₀
  Word = List A

  ∣_∣ : Word → ℕ
  ∣ w ∣ = length w

  Lang : Type₁
  Lang = ℙ Word

  _^_ : ℕ → Lang
  _^_ n w = (∣ w ∣ ≡ n) , isSetℕ (∣ w ∣) n

  _^* : Lang
  _^* w = ⊤

  _^+ : Lang
  _^+ w = ¬ ((∣ w ∣ ≡ 0) , isSetℕ (∣ w ∣) 0)

  ⟦ε⟧ : Lang
  ⟦ε⟧ = _^_ 0

  _ : _^* ≡ ⋃ ℕ (_^_)
  _ = {!!}

  _ : _^+ ≡ ⋃ ℕ (_^_ ∘ suc)
  _ = {!!}

  _ : _^* ≡ _^+ ∪ ⟦ε⟧
  _ = {!!}
