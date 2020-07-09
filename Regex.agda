{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Regex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Logic hiding ([_])
open import Cubical.HITs.SetQuotients hiding ([_])
open import Cubical.Data.Nat hiding (_+_; +-comm)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.List.Properties

open import Lang hiding (∅)
open import Fin

repeat : {A : Type₀} → ℕ → List A → List A
repeat zero xs = []
repeat (suc n) xs = xs ++ repeat n xs

module _ {A : Type₀} (IsA : IsAlphabet A) where
  data Regex : Type₀
  L : Regex → Lang IsA

  infixr 10 _+_ _·_
  infixr 11 _*
  data Regex where
    ∅ ε : Regex
    char : A → Regex
    _+_ _·_ : Regex → Regex → Regex
    _* : Regex → Regex
    --eq : ∀ x y → L x ≡ L y → x ≡ y
    --squash : isSet Regex

  L ∅ w = ⊥
  L ε w = ⟦ε⟧ IsA w
  L (char x) w = (w ≡ x ∷ []) , isOfHLevelList 0 (IsAlphabet→IsSet IsA) _ _
  L (x + y) w = (L x ∪ L y) w
  L (x · y) w =
    ∃[ u ] ∃[ v ] L x u ⊓ L y v ⊓
      ( (u ++ v ≡ w)
      , isOfHLevelList 0 (IsAlphabet→IsSet IsA) _ _
      )
  L (x *) w =
    ⋃ ℕ
      (λ n u →
        ( (u ≡ repeat n w)
        , isOfHLevelList 0 (IsAlphabet→IsSet IsA) _ _
        )
      )
      w
  --L (eq x y p i) w = p i w
  --L (squash x y p q i j) w = cong L p {!j!} w

  {-
  Languages definable by regular expressions
  -}
  RegexLangs : ℙ (Lang IsA)
  RegexLangs M = ∃[ x ∶ Regex ] (L x ≡ M) , powersets-are-sets _ _

  RegexQuot : Type₁
  RegexQuot = Regex / λ x y → L x ≡ L y

  [_] : Regex → RegexQuot
  [_] = _/_.[_]

  +-comm : ∀ {x y} → [ x + y ] ≡ [ y + x ]
  +-comm {x} {y} = eq/ _ _ (∪-comm (L x) (L y))

module example where
  A : Type₀
  A = Fin 2

  A-alph : IsAlphabet A
  A-alph = 2 , refl

  -- (0|1)*01(0|1)*
  x : Regex A-alph
  x = (char zero + char (suc zero))* · char zero · char (suc zero) · (char zero + char (suc zero))*

  P : Lang A-alph
  P [] = ⊥
  P (a ∷ []) = ⊥
  P (zero ∷ suc zero ∷ _) = ⊤
  P (zero ∷ zero ∷ w) = P (zero ∷ w)
  P (suc zero ∷ b ∷ w) = P (b ∷ w)

  L′ : Lang A-alph
  L′ = L A-alph x

  _ : L′ ≡ P
  _ = {!!}
