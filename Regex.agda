{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Regex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Logic hiding ([_])
open import Cubical.HITs.SetQuotients hiding ([_])
open import Cubical.Data.Nat hiding (_+_; +-comm)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.List.Properties

open import Common
open import Lang
open import Fin

repeat : {A : Type₀} → ℕ → List A → List A
repeat zero xs = []
repeat (suc n) xs = xs ++ repeat n xs

module _ (A : Type₀) {{isFinSetA : isFinSet A}} where
  infixr 10 _+′_ _·′_
  infixr 11 _*′
  data Regex : Type₀ where
    ∅′ ε′ : Regex
    char : A → Regex
    _+′_ _·′_ : Regex → Regex → Regex
    _*′ : Regex → Regex

module _ {A : Type₀} {{isFinSetA : isFinSet A}} where
  lang : Regex A → Lang A
  lang ∅′ w = ⊥
  lang ε′ w = ⟦ε⟧ w
  lang (char x) w = (w ≡ x ∷ []) , isOfHLevelList 0 isFinSet→isSet _ _
  lang (x +′ y) = lang x ∪ lang y
  lang (x ·′ y) w =
    ∃[ u ] ∃[ v ] lang x u ⊓ lang y v ⊓
      ( (u ++ v ≡ w)
      , isOfHLevelList 0 isFinSet→isSet _ _
      )
  lang (x *′) w =
    ⋃ ℕ
      (λ n u →
        ( (u ≡ repeat n w)
        , isOfHLevelList 0 isFinSet→isSet _ _
        )
      )
      w

  {-|
  Languages definable by regular expressions
  -}
  RegexLangs : ℙ (Lang A)
  RegexLangs M = ∃[ x ∶ Regex A ] (lang x ≡ M) , powersets-are-sets _ _

  RegexQuot : Type₁
  RegexQuot = Regex A / λ x y → lang x ≡ lang y

  [_] : Regex A → RegexQuot
  [_] = _/_.[_]

  +-comm : ∀ {x y} → [ x +′ y ] ≡ [ y +′ x ]
  +-comm {x} {y} = eq/ _ _ (∪-comm (lang x) (lang y))

private
  module example where
    A : Type₀
    A = Fin 2

    -- (0|1)*01(0|1)*
    x : Regex A
    x
      =  (char zero +′ char (suc zero))*′
      ·′ char zero ·′ char (suc zero)
      ·′ (char zero +′ char (suc zero))*′

    P : Lang A
    P [] = ⊥
    P (a ∷ []) = ⊥
    P (zero ∷ suc zero ∷ _) = ⊤
    P (zero ∷ zero ∷ w) = P (zero ∷ w)
    P (suc zero ∷ b ∷ w) = P (b ∷ w)

    L : Lang A
    L = lang x

    _ : L ≡ P
    _ = TODO
