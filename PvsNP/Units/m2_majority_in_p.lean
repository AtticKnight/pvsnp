import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Closes m2_majority_in_p with the settled unit fr_ladner: two filterMap passes
collect the falses and the trues, cpt_pair joins them, lenLE_polyTime compares
the two lengths, and a final negation flips the answer.
-/

namespace PvsNP.Units.m2_majority_in_p

/-- The falses of `x`, as a filterMap pass. -/
theorem filter_false_eq (x : List Bool) :
    x.filter (fun b => !b) =
      x.filterMap (fun b => if b = false then some b else none) := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [ih]

/-- The trues of `x`, as a filterMap pass. -/
theorem filter_true_eq (x : List Bool) :
    x.filter (fun b => b) =
      x.filterMap (fun b => if b = true then some b else none) := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [ih]

/-- The `!b` filter is the `== false` filter. -/
theorem filter_pred_false (x : List Bool) :
    x.filter (fun b => !b) = x.filter (· == false) := by
  apply List.filter_congr
  intro b _
  cases b <;> rfl

/-- The `b` filter is the `== true` filter. -/
theorem filter_pred_true (x : List Bool) :
    x.filter (fun b => b) = x.filter (· == true) := by
  apply List.filter_congr
  intro b _
  cases b <;> rfl

/-- Filter length is count. -/
theorem count_filter (b : Bool) (x : List Bool) :
    (x.filter (· == b)).length = x.count b :=
  (List.count_eq_length_filter).symm

/-- The decider answers yes exactly on the majority-true strings. -/
theorem decider_iff (x : List Bool) :
    (!(decide ((x.filter (fun b => b)).length ≤ (x.filter (fun b => !b)).length)) = true) ↔
      x.count false < x.count true := by
  rw [filter_pred_true x, filter_pred_false x, count_filter true x, count_filter false x]
  simp

/-- Collecting the falses runs in polynomial time. -/
theorem cpt_filter_false :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => x.filter (fun b => !b)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.filterMap_polyTime _ _ _
    (fun b => if b = false then some b else none) (fun x => filter_false_eq x)

/-- Collecting the trues runs in polynomial time. -/
theorem cpt_filter_true :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => x.filter (fun b => b)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.filterMap_polyTime _ _ _
    (fun b => if b = true then some b else none) (fun x => filter_true_eq x)

/-- Comparing the two lengths runs in polynomial time. -/
theorem cpt_len_le :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.LenCmp.lenLE_polyTime

/-- The unnegated comparison runs in polynomial time. -/
theorem cpt_decider_le :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) Computability.encodeBool
      (fun x => decide ((x.filter (fun b => b)).length ≤ (x.filter (fun b => !b)).length)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_pair
      cpt_filter_false cpt_filter_true) cpt_len_le

/-- Boolean negation runs in polynomial time. -/
theorem cpt_not :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      Computability.encodeBool Computability.encodeBool (fun b : Bool => !b) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.filterMap_polyTime _ _ _
    (fun b => some (!b)) (fun b => by cases b <;> rfl)

/-- The majority decider runs in polynomial time. -/
theorem cpt_decider :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) Computability.encodeBool
      (fun x => !(decide ((x.filter (fun b => b)).length ≤ (x.filter (fun b => !b)).length))) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp cpt_decider_le cpt_not

/-- The majority language is decidable in polynomial time, upstream. -/
theorem majority_in_upstream_p :
    ({x : List Bool | x.count false < x.count true} : Language Bool) ∈
      PvsNP.Units.fr_ladner.PEqualNP.Library.P := by
  have hdec : PvsNP.Units.fr_ladner.PEqualNP.Library.DecidableInPolyTime
      (fun x : List Bool => x)
      ({x : List Bool | x.count false < x.count true} : Language Bool) :=
    ⟨fun x => !(decide ((x.filter (fun b => b)).length ≤ (x.filter (fun b => !b)).length)),
     fun x => (decider_iff x).symm, cpt_decider⟩
  exact hdec

end PvsNP.Units.m2_majority_in_p

/-- The strings with more trues than falses form a language in P (TM2). -/
theorem PvsNP.Units.m2_majority_in_p :
    ({x : List Bool | x.count false < x.count true} : Language Bool) ∈ PvsNP.P :=
  (PvsNP.Units.fr_ladner.P_iff _).mpr
    PvsNP.Units.m2_majority_in_p.majority_in_upstream_p
