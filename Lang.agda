{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Logic
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.HITs.PropositionalTruncation as PT hiding (∣_∣)
open import Cubical.Relation.Nullary using (Discrete)
open import Cubical.Data.Nat
--open import Cubical.Data.Fin
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Unit.Properties
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥ renaming (⊥ to Empty)

module Lang where

open import Axioms
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

  _ᶜ : ℙ X → ℙ X
  (A ᶜ) x = ¬ A x

  de-morgan-∪-ᶜ : {A B : ℙ X} → (A ∪ B)ᶜ ≡ (A ᶜ) ∩ (B ᶜ)
  de-morgan-∪-ᶜ {A = A} {B = B} = ⊆-extensionality _ _ (⇒ , ⇐)
    where
      ⇒ : ∀ x → x ∈ ((A ∪ B)ᶜ) → x ∈ ((A ᶜ) ∩ (B ᶜ))
      ⇒ x ¬A∨B
        = (λ [A] → ¬A∨B PT.∣ ⊎.inl [A] ∣)
        , (λ [B] → ¬A∨B PT.∣ ⊎.inr [B] ∣)
      ⇐ : ∀ x → x ∈ ((A ᶜ) ∩ (B ᶜ)) → x ∈ ((A ∪ B)ᶜ)
      ⇐ x (¬A , ¬B) = PT.rec isProp⊥
        λ { (⊎.inl [A]) → ¬A [A]
          ; (⊎.inr [B]) → ¬B [B]
          }
  {-
  de-morgan-∩-ᶜ : {A B : ℙ X} → (A ∩ B)ᶜ ≡ (A ᶜ) ∪ (B ᶜ)
  de-morgan-∩-ᶜ {A = A} {B = B} = ⊆-extensionality _ _ (⇒ , ⇐)
    where
      ⇒ : ∀ x → x ∈ ((A ∩ B)ᶜ) → x ∈ ((A ᶜ) ∪ (B ᶜ))
      ⇒ x ¬A∧B = {!!}
      ⇐ : ∀ x → x ∈ ((A ᶜ) ∪ (B ᶜ)) → x ∈ ((A ∩ B)ᶜ)
      ⇐ = {!!}
  -}

  de-morgan-∩
    : {A B : ℙ X}
    → {{_ : LEM}}
    → A ∩ B ≡ ((A ᶜ) ∪ (B ᶜ))ᶜ
  de-morgan-∩ {A = A} {B = B} = ⊆-extensionality _ _ (⇒ , ⇐)
    where
      ⇒ : ∀ x → x ∈ (A ∩ B) → x ∈ (((A ᶜ) ∪ (B ᶜ))ᶜ)
      ⇒ x ([A] , [B]) = PT.rec isProp⊥
        λ { (⊎.inl ¬A) → ¬A [A]
          ; (⊎.inr ¬B) → ¬B [B]
          }
      ⇐ : ∀ x → x ∈ (((A ᶜ) ∪ (B ᶜ))ᶜ) → x ∈ (A ∩ B)
      ⇐ x ¬[¬A∨¬B]
        with classical-decide (x ∈ A) (∈-isProp A x)
           | classical-decide (x ∈ B) (∈-isProp B x)
      ... | ⊎.inl [A] | ⊎.inl [B] = [A] , [B]
      ... | ⊎.inl [A] | ⊎.inr ¬B  = ⊥.elim (¬[¬A∨¬B] PT.∣ ⊎.inr ¬B ∣)
      ... | ⊎.inr ¬A  | _         = ⊥.elim (¬[¬A∨¬B] PT.∣ ⊎.inl ¬A ∣)

module _ (A : Type₀) {{isFinSetA : isFinSet A}} where
  Word : Type₀
  Word = List A

  Lang : Type₁
  Lang = ℙ Word

∣_∣ : {A : Type₀} {{_ : isFinSet A}} → Word A → ℕ
∣ w ∣ = length w

_^_ : (A : Type₀) {{_ : isFinSet A}} → ℕ → Lang A
(A ^ n) w = (∣ w ∣ ≡ n) , isSetℕ (∣ w ∣) n

_* : (A : Type₀) {{_ : isFinSet A}} → Lang A
(A *) w = ⊤

_⁺ : (A : Type₀) {{_ : isFinSet A}} → Lang A
(A ⁺) w = ¬ ((∣ w ∣ ≡ 0) , isSetℕ (∣ w ∣) 0)

⟦ε⟧ : {A : Type₀} {{_ : isFinSet A}} → Lang A
⟦ε⟧ {A = A} = A ^ 0

module _ {A : Type₀} {{isFinSetA : isFinSet A}} where
  private
    isSet-List : isSet (List A)
    isSet-List = Discrete→isSet (discreteList isFinSet→Discrete)

  *≡⋃ : A * ≡ ⋃ ℕ (λ n → A ^ n)
  *≡⋃ = ⊆-extensionality _ _ (⇒ , ⇐)
    where
      ⇒ : ∀ w → w ∈ (A *) → w ∈ (⋃ ℕ (λ n → A ^ n))
      ⇒ w _ = PT.∣ ∣ w ∣ , refl ∣

      ⇐ : ∀ w → w ∈ (⋃ ℕ (λ n → A ^ n)) → w ∈ (A *)
      ⇐ _ _ = tt

  ⁺≡⋃ : A ⁺ ≡ ⋃ ℕ λ n → A ^ suc n
  ⁺≡⋃ = ⊆-extensionality _ _ (⇒ , ⇐)
    where
      ⇒ : ∀ w → w ∈ (A ⁺) → w ∈ (⋃ ℕ (λ n → A ^ suc n))
      ⇒ w p with ∣ w ∣
      ... | zero = ⊥.elim (p refl)
      ... | suc n = PT.∣ n , refl ∣

      ⇐ : ∀ w → w ∈ (⋃ ℕ (λ n → A ^ suc n)) → w ∈ (A ⁺)
      ⇐ w PT.∣ n , p ∣ w-empty = znots (0 ≡⟨ sym w-empty ⟩ ∣ w ∣ ≡⟨ p ⟩ suc n ∎)
      ⇐ w (squash p q i) w-empty = isProp⊥ (⇐ w p w-empty) (⇐ w q w-empty) i

  *≡⁺∪ε : A * ≡ (A ⁺) ∪ ⟦ε⟧
  *≡⁺∪ε = ⊆-extensionality _ _ (⇒ , ⇐)
    where
      ⇒ : ∀ w → w ∈ (A *) → w ∈ ((A ⁺) ∪ ⟦ε⟧)
      ⇒ w tt with ∣ w ∣
      ... | zero = PT.∣ ⊎.inr refl ∣
      ... | suc n = PT.∣ ⊎.inl (znots ∘ sym) ∣

      ⇐ : ∀ w → w ∈ ((A ⁺) ∪ ⟦ε⟧) → w ∈ (A *)
      ⇐ w x = tt

  _·_ : Lang A → Lang A → Lang A
  (L · M) w =
    ∃[ a ∶ Word A ] ∃[ b ∶ Word A ]
      L a ⊓ M b ⊓ ((a ++ b ≡ w) , isSet-List _ _)
