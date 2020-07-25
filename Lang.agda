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

open import Common
open import Fin

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

module _ (A : Type₀) {{isFinSetA : isFinSet A}} where
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
  _ = {!TODO!}

  _ : _^+ ≡ ⋃ ℕ (_^_ ∘ suc)
  _ = TODO

  _ : _^* ≡ _^+ ∪ ⟦ε⟧
  _ = TODO
