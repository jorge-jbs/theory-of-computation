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

head-maybe : List A → Maybe A
head-maybe [] = nothing
head-maybe (x ∷ _) = just x

from-maybe : A → Maybe A → A
from-maybe default nothing = default
from-maybe default (just x) = x

data Dir : Type₀ where
  left-dir right-dir : Dir

module _ {A : Type ℓ} (_≟_ : Discrete A) (blank : A) where
  mutate : A → List A → List A
  mutate z [] with z ≟ blank
  ... | yes _ = []
  ... | no _ = z ∷ []
  mutate z (x ∷ xs) = z ∷ x ∷ xs

  lin-mutate
    : ∀ {z xs}
    → LastIsNot blank xs
    → LastIsNot blank (mutate z xs)
  lin-mutate {z} {[]} lin-xs with z ≟ blank
  ... | yes _ = lin-nil
  ... | no z-neq-blank = lin-singleton z-neq-blank
  lin-mutate {z} {x ∷ xs} lin-xs = lin-cons lin-xs

  insert : A → List A → List A
  insert z [] with z ≟ blank
  ... | yes _ = []
  ... | no _ = z ∷ []
  insert z (x ∷ xs) = z ∷ x ∷ xs

  lin-insert
    : ∀ {z xs}
    → LastIsNot blank xs
    → LastIsNot blank (insert z xs)
  lin-insert {z = z} {xs = []} lin-xs with z ≟ blank
  ... | yes _ = lin-nil
  ... | no z-neq-blank = lin-singleton z-neq-blank
  lin-insert {z = z} {xs = _ ∷ _} lin-xs = lin-cons lin-xs

  move : Dir → List A → List A → List A × List A
  move left-dir [] ys = [] , insert blank ys
  move left-dir (x ∷ xs) ys = xs , insert x ys
  move right-dir xs [] = insert blank xs , []
  move right-dir xs (y ∷ ys) = insert y xs , ys

  lin-move
    : (dir : Dir)
    → {xs : List A}
    → {ys : List A}
    → LastIsNot blank xs
    → LastIsNot blank ys
    → (let xs′ , ys′ = move dir xs ys)
    -------------------------------------------
    → LastIsNot blank xs′ × LastIsNot blank ys′
  lin-move left-dir {[]} {ys} lin-xs lin-ys = lin-nil , lin-insert lin-ys
  lin-move left-dir {x ∷ .[]} {ys} (lin-singleton _) lin-ys = lin-nil , lin-insert lin-ys
  lin-move left-dir {x ∷ .(_ ∷ _)} {ys} (lin-cons lin-xs) lin-ys = lin-xs , lin-insert lin-ys
  lin-move right-dir {xs} {[]} lin-xs lin-ys = lin-insert lin-xs , lin-nil
  lin-move right-dir {xs} {y ∷ .[]} lin-xs (lin-singleton _) = lin-insert lin-xs , lin-nil
  lin-move right-dir {xs} {y ∷ .(_ ∷ _)} lin-xs (lin-cons lin-ys) = lin-insert lin-xs , lin-ys

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
        --| Symbols on the right of the head or behind it
        right : List Γ
        {-|
        We don't store the blank symbols on the right of the right-most symbol of
        the tape (except if the head is on the right of that symbol).
        -}
        last-right-not-blank : LastIsNot (⊎.inr blank) right

    data _⊢_ : Config → Config → Type₀ where
      step
        : ∀ {q p X′ left right lin-left lin-right dir}
        → (let X = from-maybe blank′ (head-maybe right))
        → δ q X ≡ just (p , X′ , dir)
        → (let right′ = mutate Discrete-Γ blank′ X′ right)
        → (let lin-right′ = lin-mutate Discrete-Γ blank′ lin-right)
        → (let left′ , right″ = move Discrete-Γ blank′ dir left right′ )
        → (let lin-left′ , lin-right″ =
                 lin-move Discrete-Γ blank′ dir lin-left lin-right′
          )
        → config q left  lin-left  right  lin-right
        ⊢ config p left′ lin-left′ right″ lin-right″

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
    -}
    lang : Lang A
    lang w =
      ∃[ p ∶ Q ]
      ∃[ l ∶ List Γ ] ∃[ lin-l ∶ LastIsNot blank′ l ]
      ∃[ r ∶ List Γ ] ∃[ lin-r ∶ LastIsNot blank′ r ]
        F p ⊓
          ∥  config init [] lin-nil (list-map ⊎.inl w) lin-map-inl
          ⊢* config p    l  lin-l   r                  lin-r
          ∥ₚ

  {-
  Languages definable by Turing machines.
  -}
  TmLangs : ℙ (Lang A)
  TmLangs L = ∃[ M ∶ TM ] (TM.lang M ≡ L) , powersets-are-sets _ _
