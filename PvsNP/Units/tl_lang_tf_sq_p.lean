import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.tl_lang_tf_n_p

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_tf_sq_p

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

private theorem mulU_len (u v : List Bool) :
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.mulU u v).length =
      u.length * v.length := by
  simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.mulU]

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

private theorem cpt_square_true :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x => PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.mulU
        (x.filter (fun b => b)) (x.filter (fun b => b))) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_mulU2 cpt_filter_true cpt_filter_true

private theorem cpt_len_le :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.LenCmp.lenLE_polyTime

private theorem le_one_in_p :
    ({x : List Bool | x.count false ≤ (x.count true) ^ 2} : Language Bool) ∈ PvsNP.P := by
  apply (PvsNP.Units.fr_ladner.P_iff _).mpr
  refine ⟨fun x => decide ((x.filter (fun b => !b)).length ≤
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.mulU
        (x.filter (fun b => b)) (x.filter (fun b => b))).length), fun x => ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, decide_eq_true_eq,
      len_filter_true, len_filter_false, mulU_len, pow_two]
  · exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_pair cpt_square_true cpt_filter_false)
      cpt_len_le

private theorem le_two_in_p :
    ({x : List Bool | (x.count true) ^ 2 ≤ x.count false} : Language Bool) ∈ PvsNP.P := by
  apply (PvsNP.Units.fr_ladner.P_iff _).mpr
  refine ⟨fun x => decide (
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.mulU
        (x.filter (fun b => b)) (x.filter (fun b => b))).length ≤
      (x.filter (fun b => !b)).length), fun x => ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, decide_eq_true_eq,
      len_filter_true, len_filter_false, mulU_len, pow_two]
  · exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_pair cpt_filter_false cpt_square_true)
      cpt_len_le

theorem count_eq_in_p :
    ({x : List Bool | x.count false = (x.count true) ^ 2} : Language Bool) ∈ PvsNP.P := by
  have hint := PvsNP.Units.m2_p_inter _ _ le_one_in_p le_two_in_p
  have heq : ({x : List Bool | x.count false ≤ (x.count true) ^ 2} : Language Bool) ⊓
      ({x : List Bool | (x.count true) ^ 2 ≤ x.count false} : Language Bool) =
      ({x : List Bool | x.count false = (x.count true) ^ 2} : Language Bool) := by
    ext x
    change (x.count false ≤ (x.count true) ^ 2 ∧ (x.count true) ^ 2 ≤ x.count false) ↔
      x.count false = (x.count true) ^ 2
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  rwa [← heq]

end PvsNP.Units.tl_lang_tf_sq_p

theorem PvsNP.Units.tl_lang_tf_sq_p :
    ({x : List Bool | ∃ n : ℕ, x = List.replicate n true ++ List.replicate (n ^ 2) false} : Language Bool) ∈ PvsNP.P := by
  have hdfa :
      ({x : List Bool | PvsNP.Units.tl_lang_tf_n_p.accept
        (x.foldl PvsNP.Units.tl_lang_tf_n_p.trans (false, false)) = true} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_dfa_in_p (Bool × Bool)
      PvsNP.Units.tl_lang_tf_n_p.trans (false, false)
      PvsNP.Units.tl_lang_tf_n_p.accept
  have hinter := PvsNP.Units.m2_p_inter _ _
    PvsNP.Units.tl_lang_tf_sq_p.count_eq_in_p hdfa
  have heq :
      (({x : List Bool | x.count false = (x.count true) ^ 2} : Language Bool) ∩
        ({x : List Bool | PvsNP.Units.tl_lang_tf_n_p.accept
          (x.foldl PvsNP.Units.tl_lang_tf_n_p.trans (false, false)) = true} : Language Bool)) =
      ({x : List Bool | ∃ n : ℕ, x = List.replicate n true ++ List.replicate (n ^ 2) false} : Language Bool) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, PvsNP.Units.tl_lang_tf_n_p.accept_iff]
    constructor
    · rintro ⟨hcnt, a, b, hx⟩
      have hb : b = a ^ 2 := by
        rw [hx, PvsNP.Units.tl_lang_tf_n_p.count_rep_true,
          PvsNP.Units.tl_lang_tf_n_p.count_rep_false] at hcnt
        exact hcnt
      subst hb
      exact ⟨a, hx⟩
    · rintro ⟨n, rfl⟩
      refine ⟨?_, n, n ^ 2, rfl⟩
      rw [PvsNP.Units.tl_lang_tf_n_p.count_rep_true,
        PvsNP.Units.tl_lang_tf_n_p.count_rep_false]
  rw [← heq]
  exact hinter
