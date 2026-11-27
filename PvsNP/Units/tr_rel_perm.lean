import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_pair_bool_combine

/-
  Original work for the make.fun desk campaign `pvsnp`, unit `tr_rel_perm`:
  whether two strings are rearrangements of each other is decidable in
  polynomial time (TM2).

  Proof idea: two lists of Bools are permutations of each other exactly when
  they have the same length and the same number of `true`s
  (`List.perm_iff_count`, the `false`-counts then following from the lengths).
  Write each `true`-count in unary by filtering for `true` (a `filterMap`,
  linear time), compare the two unary lengths — and the two lengths —
  both ways with the settled length comparison `m2_len_le_polytime`,
  and join the four comparisons with `m2_tm_pair_bool_combine`.
-/

set_option autoImplicit false

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

namespace PvsNP.Units.tr_rel_perm

/-- The unary count of `true`s in a string: keep only the `true` bits. -/
abbrev countTrueUnary : List Bool → List Bool :=
  fun l => l.filterMap (fun b => if b then some true else none)

/-- Filtering for `true` is polynomial-time: it is a `filterMap`. -/
theorem countTrueUnary_polyTime :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      countTrueUnary := by
  refine filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none) ?_
  intro a
  rfl

/-- Applying the unary `true`-count to both components of a pair. -/
theorem pairCountTrueUnary_polyTime :
    ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (countTrueUnary p.1, countTrueUnary p.2)) :=
  cpt_comp (cpt_second countTrueUnary_polyTime) (cpt_first countTrueUnary_polyTime)

/-- The length of the unary `true`-count is the number of `true`s. -/
theorem countTrueUnary_length (l : List Bool) :
    (countTrueUnary l).length = List.count true l := by
  induction l with
  | nil => simp [countTrueUnary]
  | cons b l ih => cases b <;> simp [countTrueUnary, ih]

/-- The `true`-count and the `false`-count of a string add up to its length. -/
theorem count_true_add_count_false (l : List Bool) :
    List.count true l + List.count false l = l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [ih] <;> omega

end PvsNP.Units.tr_rel_perm

/-- Whether two strings are rearrangements of each other is decidable in polynomial time (TM2). -/
theorem PvsNP.Units.tr_rel_perm :
    ∃ f : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧ ∀ p : List Bool × List Bool, (List.Perm p.1 p.2) ↔ f p = true := by
  refine ⟨fun p : List Bool × List Bool =>
    (decide ((PvsNP.Units.tr_rel_perm.countTrueUnary p.1).length ≤
        (PvsNP.Units.tr_rel_perm.countTrueUnary p.2).length) &&
      decide ((PvsNP.Units.tr_rel_perm.countTrueUnary p.2).length ≤
        (PvsNP.Units.tr_rel_perm.countTrueUnary p.1).length)) &&
    (decide (p.1.length ≤ p.2.length) && decide (p.2.length ≤ p.1.length)), ?_, ?_⟩
  · -- The decider is polynomial-time: four length comparisons joined by `&&`.
    have hLenLE : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
        (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length)) :=
      PvsNP.Units.m2_len_le_polytime
    have hLenGE : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
        (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length)) :=
      cpt_comp cpt_swap PvsNP.Units.m2_len_le_polytime
    have hCntLE : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
        (fun p : List Bool × List Bool =>
          decide ((PvsNP.Units.tr_rel_perm.countTrueUnary p.1).length ≤
            (PvsNP.Units.tr_rel_perm.countTrueUnary p.2).length)) :=
      cpt_comp PvsNP.Units.tr_rel_perm.pairCountTrueUnary_polyTime
        PvsNP.Units.m2_len_le_polytime
    have hCntGE : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
        (fun p : List Bool × List Bool =>
          decide ((PvsNP.Units.tr_rel_perm.countTrueUnary p.2).length ≤
            (PvsNP.Units.tr_rel_perm.countTrueUnary p.1).length)) :=
      cpt_comp (cpt_comp PvsNP.Units.tr_rel_perm.pairCountTrueUnary_polyTime cpt_swap)
        PvsNP.Units.m2_len_le_polytime
    exact PvsNP.Units.m2_tm_pair_bool_combine (· && ·) _ _
      (PvsNP.Units.m2_tm_pair_bool_combine (· && ·) _ _ hCntLE hCntGE)
      (PvsNP.Units.m2_tm_pair_bool_combine (· && ·) _ _ hLenLE hLenGE)
  · -- The decider is correct: permutation iff equal lengths and equal `true`-counts.
    intro p
    show List.Perm p.1 p.2 ↔
      ((decide ((PvsNP.Units.tr_rel_perm.countTrueUnary p.1).length ≤
          (PvsNP.Units.tr_rel_perm.countTrueUnary p.2).length) &&
        decide ((PvsNP.Units.tr_rel_perm.countTrueUnary p.2).length ≤
          (PvsNP.Units.tr_rel_perm.countTrueUnary p.1).length)) &&
        (decide (p.1.length ≤ p.2.length) && decide (p.2.length ≤ p.1.length))) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro hPerm
      have hcount := List.perm_iff_count.mp hPerm
      have hlen : p.1.length = p.2.length := hPerm.length_eq
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · exact le_of_eq (by
          rw [PvsNP.Units.tr_rel_perm.countTrueUnary_length,
            PvsNP.Units.tr_rel_perm.countTrueUnary_length]; exact hcount true)
      · exact le_of_eq (by
          rw [PvsNP.Units.tr_rel_perm.countTrueUnary_length,
            PvsNP.Units.tr_rel_perm.countTrueUnary_length]; exact (hcount true).symm)
      · exact le_of_eq hlen
      · exact le_of_eq hlen.symm
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have hulen : (PvsNP.Units.tr_rel_perm.countTrueUnary p.1).length =
          (PvsNP.Units.tr_rel_perm.countTrueUnary p.2).length :=
        Nat.le_antisymm h1 h2
      have hlen : p.1.length = p.2.length := Nat.le_antisymm h3 h4
      have hct : List.count true p.1 = List.count true p.2 := by
        rw [← PvsNP.Units.tr_rel_perm.countTrueUnary_length,
          ← PvsNP.Units.tr_rel_perm.countTrueUnary_length]; exact hulen
      have hcf : List.count false p.1 = List.count false p.2 := by
        have e1 := PvsNP.Units.tr_rel_perm.count_true_add_count_false p.1
        have e2 := PvsNP.Units.tr_rel_perm.count_true_add_count_false p.2
        omega
      apply List.perm_iff_count.mpr
      intro a
      cases a
      · exact hcf
      · exact hct
