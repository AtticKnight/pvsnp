import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-!
Testing whether the binary numeral `Nat.ofDigits 2 (x.map Bool.toNat)` is zero is equivalent to
checking that every bit of `x` is `false`, which is computed in polynomial time by a two-state
finite-state transducer via `fst_polyTime`.
-/

namespace PvsNP.Units.m2_tm_value_zero_test

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

def allFalseδ (q b : Bool) : Bool × Option Bool :=
  (q && !b, none)

def allFalseFin (q : Bool) : Option Bool :=
  some q

theorem ofDigits_zero_iff (x : List Bool) :
    decide (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = 0) = x.all (fun b => !b) := by
  induction x with
  | nil => simp
  | cons b t ih =>
    rw [List.map_cons, Nat.ofDigits_cons, List.all_cons]
    cases b with
    | false =>
      simp only [Bool.toNat_false, Nat.zero_add, Bool.not_false, Bool.true_and]
      have h : (2 * Nat.ofDigits 2 (t.map Bool.toNat) = 0) ↔
          (Nat.ofDigits 2 (t.map Bool.toNat) = 0) := by omega
      rw [decide_eq_decide.mpr h, ih]
    | true =>
      simp only [Bool.toNat_true, Bool.not_true, Bool.false_and]
      exact decide_eq_false (by omega)

theorem allFalse_run (x : List Bool) (q : Bool) :
    fstRun allFalseδ allFalseFin q x =
      Computability.encodeBool (q && x.all (fun b => !b)) := by
  induction x generalizing q with
  | nil =>
    cases q <;> rfl
  | cons b t ih =>
    simp only [fstRun, allFalseδ, Option.toList_none, List.nil_append, List.all_cons]
    rw [ih (q && !b), Bool.and_assoc]

end PvsNP.Units.m2_tm_value_zero_test

/-- Testing whether a binary numeral is zero takes polynomial time (TM2). -/
theorem PvsNP.Units.m2_tm_value_zero_test :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => decide (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = 0)) := by
  refine PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fst_polyTime
    PvsNP.encodeString PvsNP.encodeAnswer
    (fun x : List Bool => decide (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = 0))
    PvsNP.Units.m2_tm_value_zero_test.allFalseδ
    PvsNP.Units.m2_tm_value_zero_test.allFalseFin true ?_
  intro x
  rw [PvsNP.Units.m2_tm_value_zero_test.allFalse_run, Bool.true_and,
    PvsNP.Units.m2_tm_value_zero_test.ofDigits_zero_iff]
  rfl
