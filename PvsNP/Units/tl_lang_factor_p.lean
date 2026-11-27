import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

/-
The language of the strings holding the block [true, true, false] is accepted by a four-state
finite automaton, so it is in P by the settled unit PvsNP.Units.m2_dfa_in_p (imported, not
copied). The automaton and the proof that it accepts exactly these strings are written for this
unit.
-/

namespace PvsNP.Units.tl_lang_factor_p

/-- The transition function on the states `0`, `1`, `2` (how many bits of the block the last bits
read match) and `3` (the block has appeared). -/
def step (q : Fin 4) (b : Bool) : Fin 4 :=
  if q = 0 then (if b then 1 else 0)
  else if q = 1 then (if b then 2 else 0)
  else if q = 2 then (if b then 2 else 3)
  else 3

/-- The accepting states: the block has appeared. -/
def acc (q : Fin 4) : Bool := decide (q = 3)

/-- The bits a state stands for: the part of the block read so far (the whole block once it has
appeared). -/
def pend (q : Fin 4) : List Bool :=
  if q = 0 then [] else if q = 1 then [true] else if q = 2 then [true, true]
  else [true, true, false]

/-- A block inside `a :: m` starts at its head or lies inside `m`. -/
theorem factor_cons_iff (l : List Bool) (a : Bool) (m : List Bool) :
    l <:+: a :: m ↔ l <+: a :: m ∨ l <:+: m := by
  constructor
  · rintro ⟨s, t, h⟩
    cases s with
    | nil => exact Or.inl ⟨t, h⟩
    | cons c s =>
      rw [List.cons_append, List.cons_append] at h
      exact Or.inr ⟨s, t, (List.cons.inj h).2⟩
  · rintro (⟨t, h⟩ | ⟨s, t, h⟩)
    · exact ⟨[], t, h⟩
    · exact ⟨a :: s, t, congrArg (List.cons a) h⟩

/-- Started in the state `q`, the automaton accepts `x` exactly when the block is in the bits `q`
stands for followed by `x`. -/
theorem run_iff (x : List Bool) (q : Fin 4) :
    acc (x.foldl step q) = true ↔ [true, true, false] <:+: pend q ++ x := by
  induction x generalizing q with
  | nil => fin_cases q <;> simp [acc, pend, factor_cons_iff]
  | cons b xs ih =>
    rw [List.foldl_cons, ih]
    fin_cases q <;> cases b <;> simp [step, pend, factor_cons_iff]

/-- The language of the strings holding the block is the automaton's language. -/
theorem lang_eq :
    ({x : List Bool | [true, true, false] <:+: x} : Language Bool) =
      {x : List Bool | acc (x.foldl step 0) = true} := by
  ext x
  have h := run_iff x 0
  simp only [pend, List.nil_append, ite_true] at h
  exact h.symm

end PvsNP.Units.tl_lang_factor_p

/-- The strings holding the block [true, true, false] are in P. -/
theorem PvsNP.Units.tl_lang_factor_p : ({x : List Bool | [true, true, false] <:+: x} : Language Bool) ∈ PvsNP.P := by
  rw [PvsNP.Units.tl_lang_factor_p.lang_eq]
  exact PvsNP.Units.m2_dfa_in_p (Fin 4) PvsNP.Units.tl_lang_factor_p.step 0
    PvsNP.Units.tl_lang_factor_p.acc
