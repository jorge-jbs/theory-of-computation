{-# OPTIONS --cubical --allow-unsolved-metas #-}

module PFA where

open import Cubical.Foundations.Prelude hiding (_∎)
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Maybe
open import Cubical.Data.Prod

open import Lang
open import Fin

private variable ℓ : Level

isEmpty : Type ℓ → Type ℓ
isEmpty X = X → [ ⊥ ]

Subset : {X : Type ℓ} (P : ℙ X) → Type ℓ
Subset {X = X} P = Σ X (_∈ P)

module _ {A : Type₀} (A-alph : IsAlphabet A) where
  record PFA : Type₁ where
    field
      Q : Type₀
      Q-fin : IsFinite Q
      S : Type₀
      S-alph : IsAlphabet S
      δ : Q → Maybe A → S → ℙ (Q × List S)
      instance δ-fin : ∀ {q a s} → IsFinite (Subset (δ q a s))
      --δ : Q → Maybe A → S → Σ (ℙ (Q × List S)) (IsFinite ∘ Subset)
      initial-state : Q
      initial-symbol : S
      F : ℙ Q

    record Config : Type₀ where
      constructor config
      field
        state : Q
        word : Word A-alph
        stack : List S

    data _⊢_ : Config → Config → Type₀ where
      step-nothing
        : ∀ {q p w X α β}
        → (p , α) ∈ δ q nothing X
        → config q w (X ∷ β) ⊢ config p w (α ++ β)
      step-just
        : ∀ {q p a w X α β}
        → (p , α) ∈ δ q (just a) X
        → config q (a ∷ w) (X ∷ β) ⊢ config p w (α ++ β)

    infix  3 _∎
    infixr 2 _⊢⟨_⟩_

    data _⊢*_ : Config → Config → Type₀ where
      _∎
        : ∀ I
        → I ⊢* I
      _⊢⟨_⟩_
        : ∀ I {J K}
        → I ⊢ J
        → J ⊢* K
        → I ⊢* K

    final-state-lang : Lang A-alph
    final-state-lang w =
      ∃[ q ∶ Q ] ∃[ α ∶ List S ]
        F q ⊓
        ∥ config initial-state w (initial-symbol ∷ []) ⊢* config q [] α ∥ₚ

    empty-stack-lang : Lang A-alph
    empty-stack-lang w =
      ∃[ q ∶ Q ]
        ∥ config initial-state w (initial-symbol ∷ []) ⊢* config q [] [] ∥ₚ

  record Deterministic (M : PFA) : Type₁ where
    open PFA M
    field
      δ-isSubsingleton : ∀ q a X → isProp (Subset (δ q a X))  -- is this defined correctly?
      δ-char-inhabited→ε-empty : ∀ q a X → ∥ Subset (δ q (just a) X) ∥ → Subset (δ q nothing X) → [ ⊥ ]

  open PFA

  FinalStatePfaLangs : ℙ (Lang A-alph)
  FinalStatePfaLangs N = ∃[ M ∶ PFA ] (final-state-lang M ≡ N) , powersets-are-sets _ _

  EmptyStackPfaLangs : ℙ (Lang A-alph)
  EmptyStackPfaLangs N = ∃[ M ∶ PFA ] (empty-stack-lang M ≡ N) , powersets-are-sets _ _

  _ : FinalStatePfaLangs ≡ EmptyStackPfaLangs
  _ = {!!}

  {-
  Languages definable by pushdown finite automata
  -}
  PfaLangs : ℙ (Lang A-alph)
  PfaLangs = FinalStatePfaLangs
