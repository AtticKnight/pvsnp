import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_iff_reduces_to_true
import PvsNP.Units.m2_p_subset_np

theorem PvsNP.Units.m2_p_eq_np_iff_true_nphard :
    PvsNP.P = PvsNP.NP ↔ PvsNP.NPHard ({x : List Bool | x = [true]} : Language Bool) := by
  have reduction_iff (L : Language Bool) :
      L ∈ PvsNP.P ↔ PvsNP.KarpReducible L ({x : List Bool | x = [true]} : Language Bool) := by
    apply PvsNP.Units.m2_p_iff_reduces_to_true
  constructor
  · intro hEq
    unfold PvsNP.NPHard
    intro L hL
    apply (reduction_iff L).mp
    simpa only [hEq] using hL
  · intro hHard
    unfold PvsNP.NPHard at hHard
    refine le_antisymm PvsNP.Units.m2_p_subset_np ?_
    intro L hL
    apply (reduction_iff L).mpr
    first
    | exact hHard L hL
    | exact hHard hL
