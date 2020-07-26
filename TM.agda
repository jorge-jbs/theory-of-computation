{-# OPTIONS --cubical --allow-unsolved-metas #-}

module TM where

open import Cubical.Foundations.Prelude hiding (_∎)
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Relation.Nullary using (Discrete; yes; no)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit

open import Common
open import Lang
open import Fin

private
  variable
    ℓ : Level
    A B : Type ℓ

data LastIsNot {A : Type ℓ} (z : A) : List A → Type ℓ where
  lin-nil : LastIsNot z []
  lin-singleton : ∀ {x} → (x ≡ z → [ ⊥ ]) → LastIsNot z (x ∷ [])
  lin-cons : ∀ {x y xs} → LastIsNot z (x ∷ xs) → LastIsNot z (y ∷ x ∷ xs)

inl-neq-inr : ∀ {x : A} {y : B} → ⊎.inl x ≡ ⊎.inr y → [ ⊥ ]
inl-neq-inr {x = x} {y = y} inl-eq-inr =
  elim {C = C} (λ _ → C-inl) (λ _ → C-inr) (⊎.inr y)
  where
    C : A ⊎ B → Type _
    C (⊎.inl _) = [ ⊤ ]
    C (⊎.inr _) = [ ⊥ ]

    C-inl : C (⊎.inl x)
    C-inl = tt

    C-inr : C (⊎.inr y)
    C-inr = transport (cong C inl-eq-inr) C-inl

list-map : (A → B) → List A → List B
list-map f [] = []
list-map f (x ∷ xs) = f x ∷ list-map f xs

lin-map-inl
  : ∀ {z : B} {xs : List A}
  → LastIsNot (⊎.inr z) (list-map ⊎.inl xs)
lin-map-inl {xs = []} = lin-nil
lin-map-inl {xs = x ∷ []} = lin-singleton inl-neq-inr
lin-map-inl {xs = x ∷ y ∷ xs} = lin-cons (lin-map-inl {xs = y ∷ xs})

data Dir : Type₀ where
  left-dir right-dir : Dir

module _ {A : Type ℓ} (_≟_ : Discrete A) (blank : A) where
  move : Dir → List A → A → List A → List A × A × List A
  move left-dir [] z [] with z ≟ blank
  ... | yes _ = [] , blank , []
  ... | no _ = [] , blank , z ∷ []
  move left-dir [] z (y ∷ ys) = [] , blank , z ∷ y ∷ ys
  move left-dir (x ∷ xs) z [] with z ≟ blank
  ... | yes _ = xs , x , []
  ... | no _ = xs , x , z ∷ []
  move left-dir (x ∷ xs) z (y ∷ ys) = xs , x , z ∷ y ∷ ys
  move right-dir [] z [] with z ≟ blank
  ... | yes _ = [] , blank , []
  ... | no _ = z ∷ [] , blank , []
  move right-dir (x ∷ xs) z [] = z ∷ x ∷ xs , blank , []
  move right-dir [] z (y ∷ ys) with z ≟ blank
  ... | yes _ = [] , y , ys
  ... | no _ = z ∷ [] , y , ys
  move right-dir (x ∷ xs) z (y ∷ ys) = z ∷ x ∷ xs , y , ys

  -- This should really be automated -.-
  lin-move
    : (dir : Dir)
    → {xs : List A}
    → {z : A}
    → {ys : List A}
    → (let xs′ , z′ , ys′ = move dir xs z ys)
    → LastIsNot blank xs
    → LastIsNot blank ys
    -------------------------------------------
    → LastIsNot blank xs′ × LastIsNot blank ys′
  lin-move left-dir {[]} {z} {[]} lin-xs lin-ys with z ≟ blank
  ... | yes _ = lin-nil , lin-nil
  ... | no z-neq-blank = lin-nil , lin-singleton z-neq-blank
  lin-move left-dir {[]} {z} {y ∷ ys} lin-xs lin-ys = lin-nil , lin-cons lin-ys
  lin-move left-dir {x ∷ xs} {z} {[]} lin-xs lin-ys with z ≟ blank
  lin-move left-dir {x ∷ .[]} {z} {[]} (lin-singleton x₁) lin-ys | yes _ =
    lin-nil , lin-nil
  lin-move left-dir {x ∷ .(_ ∷ _)} {z} {[]} (lin-cons lin-xs) lin-ys | yes _ =
    lin-xs , lin-nil
  lin-move left-dir {x ∷ .[]} {z} {[]} (lin-singleton x₁) lin-ys | no z-neq-blank =
    lin-nil , lin-singleton z-neq-blank
  lin-move left-dir {x ∷ .(_ ∷ _)} {z} {[]} (lin-cons lin-xs) lin-ys | no z-neq-blank =
    lin-xs , lin-singleton z-neq-blank
  lin-move left-dir {x ∷ []} {z} {y ∷ ys} (lin-singleton _) lin-ys =
    lin-nil , lin-cons lin-ys
  lin-move left-dir {x ∷ xs} {z} {y ∷ ys} (lin-cons lin-xs) lin-ys =
    lin-xs , lin-cons lin-ys
  lin-move right-dir {[]} {z} {[]} lin-xs lin-ys with z ≟ blank
  ... | yes _ = lin-nil , lin-nil
  ... | no z-neq-blank = lin-singleton z-neq-blank , lin-nil
  lin-move right-dir {x ∷ xs} {z} {[]} lin-xs lin-ys = lin-cons lin-xs , lin-nil
  lin-move right-dir {[]} {z} {y ∷ ys} lin-xs lin-ys with z ≟ blank
  lin-move right-dir {[]} {z} {y ∷ []} lin-xs (lin-singleton x₁) | yes _ =
    lin-nil , lin-nil
  lin-move right-dir {[]} {z} {y ∷ ys} lin-xs (lin-cons lin-ys) | yes _ =
    lin-nil , lin-ys
  lin-move right-dir {[]} {z} {y ∷ []} lin-xs (lin-singleton x) | no z-neq-blank =
    lin-singleton z-neq-blank , lin-nil
  lin-move right-dir {[]} {z} {y ∷ ys} lin-xs (lin-cons lin-ys) | no z-neq-blank =
    lin-singleton z-neq-blank , lin-ys
  lin-move right-dir {x ∷ xs} {z} {y ∷ .[]} lin-xs (lin-singleton _) =
    lin-cons lin-xs , lin-nil
  lin-move right-dir {x ∷ xs} {z} {y ∷ .(_ ∷ _)} lin-xs (lin-cons lin-ys) =
    lin-cons lin-xs , lin-ys

module _ (A : Type₀) {{isFinSetA : isFinSet A}} where
  --| Turing machines over an alphabet A.
  record TM : Type₁ where
    field
      --| States.
      Q : Type₀
      {{isFinSetQ}} : isFinSet Q
      --| Symbols exclusively for the tape.
      S : Type₀
      {{isFinSetS}} : isFinSet S

    {-|
    The tape symbols (i.e. the input symbols plus the exclusively tape symbols).
    -}
    Γ : Type₀
    Γ = A ⊎ S

    Discrete-Γ : Discrete Γ
    Discrete-Γ = isFinSet→Discrete

    field
      --| Transition function.
      δ : Q → Γ → Maybe (Q × Γ × Dir)
      --| Initial state.
      init : Q
      --| Blank symbol.
      blank : S
      --| Accepting states.
      F : ℙ Q

    blank′ = ⊎.inr blank

    record Config : Type₀ where
      constructor config
      field
        --| Current state
        state : Q
        --| Symbols on the left of the head
        left : List Γ
        {-
        TODO: is this the best way to do it? We could consider:

        - Using HITs: would it make it more pleasant?
        - Ignoring this condition: would it be a good definition of
          configurations?
        -}
        {-|
        We don't store the blank symbols on the left of the left-most symbol of
        the tape (except if the head is on the left of that symbol).
        -}
        last-left-not-blank : LastIsNot (⊎.inr blank) left
        --| Symbol behind head
        head : Γ
        --| Symbols on the right of the head
        right : List Γ
        {-|
        We don't store the blank symbols on the right of the right-most symbol of
        the tape (except if the head is on the right of that symbol).
        -}
        last-right-not-blank : LastIsNot (⊎.inr blank) right

    data _⊢_ : Config → Config → Type₀ where
      step
        : ∀ {q p X X′ left right lin-left lin-right dir}
        → δ q X ≡ just (p , X′ , dir)
        → (let left′ , Y , right′ = move Discrete-Γ blank′ dir left X′ right )
        → (let lin-left′ , lin-right′ =
                 lin-move Discrete-Γ blank′ dir lin-left lin-right
          )
        → config q left  lin-left  X right  lin-right
        ⊢ config p left′ lin-left′ Y right′ lin-right′

    {-|
    Turing Machines can step from one configuration to another in only one
    way.
    -}
    isProp-⊢ : ∀ {C D} → isProp (C ⊢ D)
    isProp-⊢ = TODO

    {-|
    Given a Turing Machine configuration, there is only one configuration
    that goes after it, or none.
    -}
    tm-deterministic : ∀ {C} → isProp (Σ[ D ∈ Config ] C ⊢ D)
    tm-deterministic = TODO

    infix  3 _∎
    infixr 2 _⊢⟨_⟩_

    --| The transitive closure of `_⊢_`.
    data _⊢*_ : Config → Config → Type₀ where
      _∎
        : ∀ I
        → I ⊢* I
      _⊢⟨_⟩_
        : ∀ I {J K}
        → I ⊢ J
        → J ⊢* K
        → I ⊢* K

    {-|
    The language accepted by a Turing Machine.

    The input is placed one cell at the right of the head. That means that the
    head is blank initially.
    -}
    lang : Lang A
    lang w =
      ∃[ p ∶ Q ]
      ∃[ l ∶ List Γ ] ∃[ lin-l ∶ LastIsNot blank′ l ]
      ∃[ h ∶ Γ ]
      ∃[ r ∶ List Γ ] ∃[ lin-r ∶ LastIsNot blank′ r ]
        F p ⊓
          ∥  config init [] lin-nil blank′ (list-map ⊎.inl w) lin-map-inl
          ⊢* config p    l  lin-l   h      r                  lin-r
          ∥ₚ

  {-
  Languages definable by Turing machines.
  -}
  TmLangs : ℙ (Lang A)
  TmLangs L = ∃[ M ∶ TM ] (TM.lang M ≡ L) , powersets-are-sets _ _
