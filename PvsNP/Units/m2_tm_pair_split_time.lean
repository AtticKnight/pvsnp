import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_linear_clock

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_pair_split_time

open Turing PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

/-- One-state transducer copying the left-tagged bits and dropping the right-tagged ones. -/
def fstδ : Unit → (Bool ⊕ Bool) → Unit × Option Bool × Option Bool
  | _, Sum.inl b => ((), some b, none)
  | _, Sum.inr _ => ((), none, none)

/-- One-state transducer dropping the left-tagged bits and copying the right-tagged ones. -/
def sndδ : Unit → (Bool ⊕ Bool) → Unit × Option Bool × Option Bool
  | _, Sum.inl _ => ((), none, none)
  | _, Sum.inr b => ((), some b, none)

/-- One-state transducer copying every bit, whatever its tag. -/
def catδ : Unit → (Bool ⊕ Bool) → Unit × Option Bool × Option Bool
  | _, Sum.inl b => ((), some b, none)
  | _, Sum.inr b => ((), some b, none)

/-- No output at the end of the input. -/
def noFin : Unit → Option Bool := fun _ => none

theorem fst_run_drop (y : List Bool) :
    fstRun2 fstδ noFin () (y.map Sum.inr) = [] := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [fstRun2, fstδ, ih]

theorem fst_run (x y : List Bool) :
    fstRun2 fstδ noFin () (x.map Sum.inl ++ y.map Sum.inr) = x := by
  induction x with
  | nil => simp [fst_run_drop]
  | cons b x ih => simp [fstRun2, fstδ, ih]

theorem snd_run_drop (x : List Bool) :
    fstRun2 sndδ noFin () (x.map Sum.inl) = [] := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [fstRun2, sndδ, ih]

theorem snd_run_prefix (x : List Bool) (l : List (Bool ⊕ Bool)) :
    fstRun2 sndδ noFin () (x.map Sum.inl ++ l) = fstRun2 sndδ noFin () l := by
  induction x with
  | nil => simp
  | cons b x ih => simp [fstRun2, sndδ, ih]

theorem snd_run_inr (y : List Bool) :
    fstRun2 sndδ noFin () (y.map Sum.inr) = y := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [fstRun2, sndδ, ih]

theorem snd_run (x y : List Bool) :
    fstRun2 sndδ noFin () (x.map Sum.inl ++ y.map Sum.inr) = y := by
  rw [snd_run_prefix, snd_run_inr]

theorem cat_run_inr (y : List Bool) :
    fstRun2 catδ noFin () (y.map Sum.inr) = y := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [fstRun2, catδ, ih]

theorem cat_run (x y : List Bool) :
    fstRun2 catδ noFin () (x.map Sum.inl ++ y.map Sum.inr) = x ++ y := by
  induction x with
  | nil => simp [cat_run_inr]
  | cons b x ih => simp [fstRun2, catδ, ih]

/-- The first component, within `2 * n + 3` steps. -/
theorem fst_time : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime PvsNP.encodePair
    PvsNP.encodeString (fun p : List Bool × List Bool => p.1) (fun n => 2 * n + 3) :=
  PvsNP.Units.m2_linear_clock.fst2_time _ _ _ fstδ noFin () (fun p => (fst_run p.1 p.2).symm)

/-- The second component, within `2 * n + 3` steps. -/
theorem snd_time : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime PvsNP.encodePair
    PvsNP.encodeString (fun p : List Bool × List Bool => p.2) (fun n => 2 * n + 3) :=
  PvsNP.Units.m2_linear_clock.fst2_time _ _ _ sndδ noFin () (fun p => (snd_run p.1 p.2).symm)

/-- The concatenation, within `2 * n + 3` steps. -/
theorem cat_time : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime PvsNP.encodePair
    PvsNP.encodeString (fun p : List Bool × List Bool => p.1 ++ p.2) (fun n => 2 * n + 3) :=
  PvsNP.Units.m2_linear_clock.fst2_time _ _ _ catδ noFin () (fun p => (cat_run p.1 p.2).symm)

end PvsNP.Units.m2_tm_pair_split_time

/-- Each part of the written pair, and their concatenation, within 2n + 3 steps (TM2). -/
theorem PvsNP.Units.m2_tm_pair_split_time :
    (∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => p.1),
      ∀ n : ℕ, M.time n ≤ 2 * n + 3) ∧
    (∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => p.2),
      ∀ n : ℕ, M.time n ≤ 2 * n + 3) ∧
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => p.1 ++ p.2),
      ∀ n : ℕ, M.time n ≤ 2 * n + 3 :=
  ⟨PvsNP.Units.m2_tm_pair_split_time.fst_time,
    PvsNP.Units.m2_tm_pair_split_time.snd_time,
    PvsNP.Units.m2_tm_pair_split_time.cat_time⟩
