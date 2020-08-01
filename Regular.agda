{-# OPTIONS --cubical #-}

module Regular where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
open import Cubical.HITs.PropositionalTruncation as PT

open import Axioms
open import Common
open import Fin
open import Lang
open import Regex

private
  variable
    ℓ : Level

isRegular : {A : Type₀} {{isFinSet-A : isFinSet A}} → Lang A → Type₁
isRegular w = w ∈ RegexLangs

rec2′ : ∀ {A B P : Type ℓ} → isProp P → (A → B → P) → ∥ A ∥ → ∥ B ∥ → P
rec2′ Pprop f =
  rec (isPropΠ (λ _ → Pprop))
    (λ a → rec Pprop (f a))

module _
    {A : Type₀}
    {{isFinSet-A : isFinSet A}}
    {L M : Lang A}
    {{isRegular-L : isRegular L}}
    {{isRegular-M : isRegular M}}
    where
  instance
    reg-closed-under-∪ : isRegular (L ∪ M)
    reg-closed-under-∪ = prf it it
      where
        prf : isRegular L → isRegular M → isRegular (L ∪ M)
        prf = rec2′ squash λ (x , lang-x≡L) (y , lang-y≡M) →
            ∥_∥.∣
              ( x +′ y
              , ( lang (x +′ y) ≡⟨ refl ⟩
                  lang x ∪ lang y ≡⟨ cong₂ _∪_ lang-x≡L lang-y≡M ⟩
                  L ∪ M ∎
                )
              )
            ∣

module _
    {A : Type₀}
    {{isFinSet-A : isFinSet A}}
    {L : Lang A}
    {{isRegular-L : isRegular L}}
    where
  instance
    reg-closed-under-¬ : isRegular (L ᶜ)
    reg-closed-under-¬ = TODO

module _
    {A : Type₀}
    {{isFinSet-A : isFinSet A}}
    {L M : Lang A}
    {{isRegular-L : isRegular L}}
    {{isRegular-M : isRegular M}}
    where
  instance
    reg-closed-under-∩ : {{_ : LEM}} → isRegular (L ∩ M)
    reg-closed-under-∩ = proof
      where
        lemma : isRegular (((L ᶜ) ∪ (M ᶜ))ᶜ)
        lemma = it

        proof : isRegular (L ∩ M)
        proof = subst
          isRegular
          (sym (de-morgan-∩ {A = L} {B = M}))
          lemma
