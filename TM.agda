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
open import Cubical.Codata.Stream
open Stream

open import Common
open import Lang
open import Fin

private
  variable
    ℓ : Level
    A B : Type ℓ

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

head-maybe : List A → Maybe A
head-maybe [] = nothing
head-maybe (x ∷ _) = just x

from-maybe : A → Maybe A → A
from-maybe default nothing = default
from-maybe default (just x) = x

_∷ₛ_ : A → Stream A → Stream A
head (x ∷ₛ xs) = x
tail (x ∷ₛ xs) = xs

repeat : A → Stream A
head (repeat x) = x
tail (repeat x) = repeat x

data Suffix {A : Type₀} : Stream A → Stream A → Type₀ where
  here : ∀ {xs} → Suffix xs xs
  there : ∀ {xs y ys} → Suffix xs ys → Suffix xs (y , ys)

from-list : A → List A → Stream A
from-list z [] = repeat z
from-list z (x ∷ xs) = x ∷ₛ from-list z xs

data Dir : Type₀ where
  left-dir right-dir : Dir

module _ (A : Type₀) {{isFinSetA : isFinSet A}} where
  --| Turing machines over an alphabet A.
  record TM : Type₁ where
    field
      --| States.
      State : Type₀
      {{isFinSetState}} : isFinSet State
      --| Symbols exclusively for the tape.
      InternalSymbol : Type₀
      {{isFinSetInternalSymbol}} : isFinSet InternalSymbol

    {-|
    The tape symbols (i.e. the input symbols plus the exclusively tape symbols).
    -}
    TapeSymbol : Type₀
    TapeSymbol = A ⊎ InternalSymbol

    field
      --| Transition function.
      δ : State → TapeSymbol → State × TapeSymbol × Dir
      --| Initial state.
      init : State
      --| Blank symbol.
      blank : InternalSymbol
      {-|
      Accepting states.

      A Turing machine can only halt by reaching a final state, and it always
      halts when it reaches a final state.
      -}
      FinalState : ℙ State

    blank′ = ⊎.inr blank

    record Tape : Type₀ where
      constructor mk-tape
      field
        --| Symbols on the left of the head.
        left : Stream TapeSymbol
        --| Symbols on the head of the tape.
        head : TapeSymbol
        --| Symbols on the right of the head.
        right : Stream TapeSymbol

    blanks : Stream TapeSymbol
    blanks = repeat blank′

    {-|
    We say a stream is bounded when, past a point, all its elements are repeated.
    Or, in other words, it has a suffix of the form `repeat z` for some z.
    -}
    IsBoundedStream : Stream TapeSymbol → Type₀
    IsBoundedStream = Suffix blanks

    IsBoundedTape : Tape → Type₀
    IsBoundedTape (mk-tape l _ r) = IsBoundedStream l × IsBoundedStream r

    move : Dir → Tape → Tape
    Tape.left (move left-dir (mk-tape l h r)) = l .tail
    Tape.head (move left-dir (mk-tape l h r)) = l .head
    Tape.right (move left-dir (mk-tape l h r)) = h ∷ₛ r
    Tape.left (move right-dir (mk-tape l h r)) = h ∷ₛ l
    Tape.head (move right-dir (mk-tape l h r)) = r .head
    Tape.right (move right-dir (mk-tape l h r)) = r .tail

    initial-tape : List A → Tape
    Tape.left (initial-tape xs) = blanks
    Tape.head (initial-tape []) = blank′
    Tape.head (initial-tape (x ∷ xs)) = ⊎.inl x
    Tape.right (initial-tape []) = blanks
    Tape.right (initial-tape (x ∷ xs)) = from-list blank′ (list-map ⊎.inl xs)

    record Config : Type₀ where
      constructor config
      field
        --| Current state.
        state : State
        --| The tape.
        tape : Tape

    data _⊢_ : Config → Config → Type₀ where
      step
        : ∀ {q l h r}
        → (let p , h′ , dir = δ q h)
        → config q (mk-tape l h r)
        ⊢ config p (move dir (mk-tape l h′ r))

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
    lang w = ∃[ p ∶ State ] ∃[ final-tape ∶ Tape ]
      FinalState p ⊓ ∥ config init (initial-tape w) ⊢* config p final-tape ∥ₚ

  module _ (M : TM) where
    open TM M

    {-|
    A Turing Machine can only read/write finitely many cells in finite time.

    Note: assumming all Turing Machines start with the tape `initial-tape w`
    where `w` is the input to the machine.
    -}
    is-bounded-tape
      : ∀ {w C}
      → config init (initial-tape w) ⊢* C
      → IsBoundedTape (Config.tape C)
    is-bounded-tape = TODO

  {-|
  Languages definable by Turing machines.
  -}
  TmLangs : ℙ (Lang A)
  TmLangs L = ∃[ M ∶ TM ] (TM.lang M ≡ L) , powersets-are-sets _ _
