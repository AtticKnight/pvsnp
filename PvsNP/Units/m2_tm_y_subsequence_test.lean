import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tr_rel_sublist

/-- The verified subsequence machine returns the canonical Boolean decision. -/
theorem PvsNP.Units.m2_tm_y_subsequence_test :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (List.Sublist p.1 p.2)) := by
  obtain ⟨f, machine, correct⟩ := PvsNP.Units.tr_rel_sublist
  have agrees : f = (fun p : List Bool × List Bool => decide (List.Sublist p.1 p.2)) := by
    funext p
    apply Bool.eq_iff_iff.2
    simpa only [decide_eq_true_eq] using (correct p).symm
  rw [← agrees]
  exact machine
