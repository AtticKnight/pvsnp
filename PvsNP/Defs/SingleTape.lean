import Mathlib.Computability.Language
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.PostTuringMachine
import PvsNP.Defs.Encoding

/-!
# The single-tape side

The textbook classes are defined with single-tape Turing machines; this campaign's own classes
(`PvsNP.P`, `PvsNP.NP`, …) are defined with Mathlib's multi-stack machines. The bridge between the
two is work posted as units; this file holds only the names needed to state it: a single-tape
machine, what it means for one to compute a function in polynomial time, and the same classes
built on that notion, under the namespace `PvsNP.SingleTape`.

The machine is Mathlib's single-tape Turing machine `Turing.TM0.Machine`: a finite set of states
`Λ` with a start state (its `default`), a finite tape alphabet `Γ` with a blank (its `default`), a
tape infinite in both directions, and a transition function that, given the state and the symbol
under the head, either halts (`none`) or names the next state and one action, writing a symbol or
moving the head one cell left or right. (A textbook step writes and moves at once; here that is two
steps, which changes running times by at most a factor of two.)

On top of Mathlib's machine, a `PvsNP.SingleTape.Machine A B` fixes how strings are written:

* an input string over `A` is written from the head rightwards, one tape symbol per letter
  (`inp`), on an otherwise blank tape, and the machine starts in its start state;
* an output string over `B` is read, once the machine has halted, from the head rightwards
  (`out`): the output is `r` when the cells from the head on hold `r` followed by a symbol that is
  no output letter.

Input and output letters are distinct tape symbols, none of them the blank. A running time is
the number of steps before the machine halts, Mathlib's `StateTransition.EvalsToInTime` over
Mathlib's `Turing.TM0.step`: the same count `Turing.TM2OutputsInTime` uses on the multi-stack
side.
-/

set_option autoImplicit false

namespace PvsNP.SingleTape

/-- A single-tape Turing machine reading strings over `A` and writing strings over `B`:
Mathlib's `Turing.TM0.Machine` over a finite tape alphabet `Γ` (its `default` the blank) and a
finite set of states `Λ` (its `default` the start state), with the tape symbols `inp a` and
`out b` that write the letters of an input and of an output. -/
structure Machine (A B : Type) where
  /-- The tape alphabet. -/
  Γ : Type
  /-- The states. -/
  Λ : Type
  /-- The blank symbol is `default`. -/
  [blank : Inhabited Γ]
  /-- The start state is `default`. -/
  [start : Inhabited Λ]
  /-- The tape alphabet is finite. -/
  [fintypeΓ : Fintype Γ]
  /-- There are finitely many states. -/
  [fintypeΛ : Fintype Λ]
  /-- The tape symbol of each input letter. -/
  inp : A → Γ
  /-- The tape symbol of each output letter. -/
  out : B → Γ
  /-- Distinct input letters are distinct symbols. -/
  inp_injective : Function.Injective inp
  /-- Distinct output letters are distinct symbols. -/
  out_injective : Function.Injective out
  /-- No input letter is the blank. -/
  inp_ne_blank : ∀ a : A, inp a ≠ default
  /-- No output letter is the blank. -/
  out_ne_blank : ∀ b : B, out b ≠ default
  /-- The transition function: from a state and the symbol under the head, `none` to halt, or
  the next state and one action (write a symbol, or move left or right). -/
  δ : Turing.TM0.Machine Γ Λ

namespace Machine

variable {A B : Type} (M : Machine A B)

/-- The blank of `M`'s tape alphabet. -/
instance inhabitedΓ : Inhabited M.Γ :=
  M.blank

/-- The start state of `M`. -/
instance inhabitedΛ : Inhabited M.Λ :=
  M.start

/-- A configuration of `M`: its state and its tape (Mathlib's `Turing.TM0.Cfg`). -/
abbrev Cfg : Type :=
  Turing.TM0.Cfg M.Γ M.Λ

/-- One step of `M` (Mathlib's `Turing.TM0.step`): `none` when `M` halts in the configuration. -/
def step : M.Cfg → Option M.Cfg :=
  Turing.TM0.step M.δ

/-- The starting configuration on the input `s`: the start state, the head on the first cell of
`s` written by `inp`, blanks everywhere else (Mathlib's `Turing.TM0.init`). -/
def init (s : List A) : M.Cfg :=
  Turing.TM0.init (s.map M.inp)

/-- In the configuration `c`, the cells from the head rightwards hold the string `r` written by
`out`, followed by a symbol that is no output letter. -/
def Shows (c : M.Cfg) (r : List B) : Prop :=
  (∀ (i : ℕ) (h : i < r.length), (Turing.TM0.Cfg.Tape c).right₀.nth i = M.out (r[i]'h)) ∧
    ∀ b : B, (Turing.TM0.Cfg.Tape c).right₀.nth r.length ≠ M.out b

/-- Started on the input `s`, `M` halts within `t` steps with the output `r`: from `M.init s` it
reaches, in at most `t` steps, a configuration in which it halts and which shows `r`. -/
def OutputsInTime (s : List A) (r : List B) (t : ℕ) : Prop :=
  ∃ c : M.Cfg,
    Nonempty (StateTransition.EvalsToInTime M.step (M.init s) (some c) t) ∧
      M.step c = none ∧ M.Shows c r

end Machine

/-- `f` is computable in polynomial time on a single-tape machine, its inputs written by `ea` and
its outputs by `eb`: some single-tape machine, on every input `ea a`, halts with the output
`eb (f a)` within a number of steps bounded by a polynomial in the length of `ea a`. -/
def PolyTimeComputable {α β A B : Type} (ea : α → List A) (eb : β → List B) (f : α → β) :
    Prop :=
  ∃ (M : Machine A B) (p : Polynomial ℕ),
    ∀ a : α, M.OutputsInTime (ea a) (eb (f a)) (p.eval (ea a).length)

/-- `L` is decidable in polynomial time on a single-tape machine: a yes/no function on binary
strings that answers yes exactly on the members of `L` is computable in polynomial time on a
single-tape machine. -/
def PolyTimeDecidable (L : Language Bool) : Prop :=
  ∃ f : List Bool → Bool,
    PvsNP.SingleTape.PolyTimeComputable encodeString encodeAnswer f ∧
      ∀ x : List Bool, x ∈ L ↔ f x = true

/-- The class P on single-tape machines. -/
def P : Set (Language Bool) :=
  {L | PvsNP.SingleTape.PolyTimeDecidable L}

/-- `V` is a single-tape polynomial-time verifier for `L` with certificates of length at most `p`:
as `PvsNP.PolyTimeVerifier`, with `V` computable in polynomial time on a single-tape machine. -/
def PolyTimeVerifier (L : Language Bool) (V : List Bool × List Bool → Bool) (p : Polynomial ℕ) :
    Prop :=
  PvsNP.SingleTape.PolyTimeComputable encodePair encodeAnswer V ∧
    ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ V (x, w) = true

/-- The class NP on single-tape machines. -/
def NP : Set (Language Bool) :=
  {L | ∃ (V : List Bool × List Bool → Bool) (p : Polynomial ℕ),
    PvsNP.SingleTape.PolyTimeVerifier L V p}

/-- The class coNP on single-tape machines. -/
def coNP : Set (Language Bool) :=
  {L | Lᶜ ∈ PvsNP.SingleTape.NP}

/-- `L₁` is Karp reducible to `L₂` on single-tape machines: as `PvsNP.KarpReducible`, with the
reduction computable in polynomial time on a single-tape machine. -/
def KarpReducible (L₁ L₂ : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool,
    PvsNP.SingleTape.PolyTimeComputable encodeString encodeString f ∧
      ∀ x : List Bool, x ∈ L₁ ↔ f x ∈ L₂

/-- `L` is NP-hard on single-tape machines. -/
def NPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ PvsNP.SingleTape.NP, PvsNP.SingleTape.KarpReducible L' L

/-- `L` is NP-complete on single-tape machines. -/
def NPComplete (L : Language Bool) : Prop :=
  L ∈ PvsNP.SingleTape.NP ∧ PvsNP.SingleTape.NPHard L

end PvsNP.SingleTape
