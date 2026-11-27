import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_p_inter

/-
Adapted from the settled units PvsNP.Units.fr_ladner and PvsNP.Units.m2_majority_in_p
of github.com/makedotfun/pvsnp (Apache License 2.0): two filterMap passes collect trues
and falses, cpt_app2 doubles the falses, lenLE_polyTime checks both inequalities, and
m2_p_inter intersects the two P languages.
-/

namespace PvsNP.Units.tl_lang_count_twice_p

private theorem filter_false_eq (x : List Bool) :
    x.filter (fun b => !b) =
      x.filterMap (fun b => if b = false then some b else none) := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [ih]

private theorem filter_true_eq (x : List Bool) :
    x.filter (fun b => b) =
      x.filterMap (fun b => if b = true then some b else none) := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [ih]

private theorem len_filter_false (x : List Bool) :
    (x.filter (fun b => !b)).length = x.count false := by
  have h : x.filter (fun b => !b) = x.filter (· == false) :=
    List.filter_congr (fun b _ => by cases b <;> rfl)
  rw [h, List.count_eq_length_filter]

private theorem len_filter_true (x : List Bool) :
    (x.filter (fun b => b)).length = x.count true := by
  have h : x.filter (fun b => b) = x.filter (· == true) :=
    List.filter_congr (fun b _ => by cases b <;> rfl)
  rw [h, List.count_eq_length_filter]

private theorem cpt_filter_false :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => x.filter (fun b => !b)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.filterMap_polyTime _ _ _
    (fun b => if b = false then some b else none) filter_false_eq

private theorem cpt_filter_true :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => x.filter (fun b => b)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.filterMap_polyTime _ _ _
    (fun b => if b = true then some b else none) filter_true_eq

private theorem cpt_double_false :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => x.filter (fun b => !b) ++ x.filter (fun b => !b)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2 cpt_filter_false cpt_filter_false

private theorem cpt_len_le :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.LenCmp.lenLE_polyTime

private theorem le_one_in_p :
    ({x : List Bool | x.count true ≤ 2 * x.count false} : Language Bool) ∈ PvsNP.P := by
  apply (PvsNP.Units.fr_ladner.P_iff _).mpr
  refine ⟨fun x => decide ((x.filter (fun b => b)).length ≤
      (x.filter (fun b => !b) ++ x.filter (fun b => !b)).length), fun x => ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, decide_eq_true_eq, List.length_append,
      len_filter_true, len_filter_false]
    omega
  · exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_pair cpt_double_false cpt_filter_true)
      cpt_len_le

private theorem le_two_in_p :
    ({x : List Bool | 2 * x.count false ≤ x.count true} : Language Bool) ∈ PvsNP.P := by
  apply (PvsNP.Units.fr_ladner.P_iff _).mpr
  refine ⟨fun x => decide ((x.filter (fun b => !b) ++ x.filter (fun b => !b)).length ≤
      (x.filter (fun b => b)).length), fun x => ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, decide_eq_true_eq, List.length_append,
      len_filter_true, len_filter_false]
    omega
  · exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_pair cpt_filter_true cpt_double_false)
      cpt_len_le

theorem main :
    ({x : List Bool | x.count true = 2 * x.count false} : Language Bool) ∈ PvsNP.P := by
  have hint := PvsNP.Units.m2_p_inter _ _ le_one_in_p le_two_in_p
  have heq : ({x : List Bool | x.count true ≤ 2 * x.count false} : Language Bool) ⊓
      ({x : List Bool | 2 * x.count false ≤ x.count true} : Language Bool) =
      ({x : List Bool | x.count true = 2 * x.count false} : Language Bool) := by
    ext x
    change (x.count true ≤ 2 * x.count false ∧ 2 * x.count false ≤ x.count true) ↔
      x.count true = 2 * x.count false
    omega
  rwa [← heq]

end PvsNP.Units.tl_lang_count_twice_p

theorem PvsNP.Units.tl_lang_count_twice_p :
    ({x : List Bool | x.count true = 2 * x.count false} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_count_twice_p.main
