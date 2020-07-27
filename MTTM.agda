{-# OPTIONS --cubical --allow-unsolved-metas #-}

module MTTM where

open import Cubical.Foundations.Prelude hiding (_∎)
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Relation.Nullary using (Discrete; yes; no)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Vec as Vec hiding (head; tail)
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit
open import Cubical.Codata.Stream
open Stream

open import ForUpstream.Codata.Stream as S
open import ForUpstream.Data.List as L
open import ForUpstream.Data.Vec as V
open import Common
open import Lang
open import Fin

private
  variable
    ℓ : Level
    A B C : Type ℓ

data Dir : Type₀ where
  left-dir right-dir : Dir

module _ (A : Type₀) {{isFinSetA : isFinSet A}} where
  --| Multi-tape Turing machines over an alphabet A.
  record MTTM : Type₁ where
    field
      --| States.
      State : Type₀
      {{isFinSetState}} : isFinSet State
      --| Symbols exclusively for the tape.
      InternalSymbol : Type₀
      {{isFinSetInternalSymbol}} : isFinSet InternalSymbol
      --| Number of work tapes
      num-work-tapes : ℕ

    {-|
    The tape symbols (i.e. the input symbols plus the exclusively tape symbols).
    -}
    TapeSymbol : Type₀
    TapeSymbol = A ⊎ InternalSymbol

    {-|
    Total number of tapes (i.e. the number of work tapes plus one for the input
    tape).
    -}
    num-tapes : ℕ
    num-tapes = suc num-work-tapes

    field
      --| Transition function.
      δ
        : State
        → Vec TapeSymbol num-tapes
        → State × Vec (TapeSymbol × Dir) num-tapes
      --| Initial state.
      init : State
      --| Blank symbol.
      blank : InternalSymbol
      {-|
      Accepting states.

      A multi-tape Turing machine can only halt by reaching a final state, and
      it always halts when it reaches a final state.
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

    Tapes : Type₀
    Tapes = Vec Tape num-tapes

    heads : Tapes → Vec TapeSymbol num-tapes
    heads = Vec.map Tape.head

    blanks : Stream TapeSymbol
    blanks = S.repeat blank′

    blank-tape : Tape
    Tape.left blank-tape = blanks
    Tape.head blank-tape = blank′
    Tape.right blank-tape = blanks

    {-|
    We say a stream is bounded when, past a point, all its elements are the same.
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

    move-all : Tapes → Vec (TapeSymbol × Dir) num-tapes → Tapes
    move-all tapes heads-and-dirs =
      V.map₂
        (λ (mk-tape l h r) (h′ , dir) → move dir (mk-tape l h′ r))
        tapes
        heads-and-dirs

    initial-input-tape : List A → Tape
    Tape.left (initial-input-tape xs) = blanks
    Tape.head (initial-input-tape []) = blank′
    Tape.head (initial-input-tape (x ∷ xs)) = ⊎.inl x
    Tape.right (initial-input-tape []) = blanks
    Tape.right (initial-input-tape (x ∷ xs)) = from-list blank′ (L.map ⊎.inl xs)

    initial-tapes : List A → Tapes
    initial-tapes w = initial-input-tape w ∷ V.repeat blank-tape

    record Config : Type₀ where
      constructor config
      field
        --| Current state.
        state : State
        --| The tapes.
        tapes : Tapes

    data _⊢_ : Config → Config → Type₀ where
      step
        : ∀ {q tapes}
        → (let p , heads-and-dirs = δ q (heads tapes))
        → config q tapes ⊢ config p (move-all tapes heads-and-dirs)

    {-|
    Multi-tape multi-tape Turing machines can step from one configuration to
    another in only one way.
    -}
    isProp-⊢ : ∀ {C D} → isProp (C ⊢ D)
    isProp-⊢ = TODO

    {-|
    Given a multi-tape multi-tape Turing machine configuration, there is only
    one configuration that goes after it, or none.
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
    The language accepted by a multi-tape multi-tape Turing machine.
    -}
    lang : Lang A
    lang w = ∃[ p ∶ State ] ∃[ final-tapes ∶ Tapes ]
      FinalState p ⊓ ∥ config init (initial-tapes w) ⊢* config p final-tapes ∥ₚ

  module _ (M : MTTM) where
    open MTTM M

    {-
    {-|
    A multi-tape multi-tape Turing machine can only read/write finitely many
    cells in finite time.

    Note: assumming all multi-tape multi-tape Turing machines start with the
    tapes `initial-tapes w` where `w` is the input to the machine.
    -}
    is-bounded-tape
      : ∀ {w C}
      → config init (initial-tape w) ⊢* C
      → IsBoundedTape (Config.tape C)
    is-bounded-tape = TODO
    -}

  {-|
  Languages definable by multi-tape multi-tape Turing machines.
  -}
  MttmLangs : ℙ (Lang A)
  MttmLangs L = ∃[ M ∶ MTTM ] (MTTM.lang M ≡ L) , powersets-are-sets _ _
