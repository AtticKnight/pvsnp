import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_ww_in_p
import PvsNP.Units.tf_fun_ones_unary

/-- The strings whose trues, written in unary, form a string written twice are in P (TM2).

The map `x ↦ List.replicate (x.count true) true` is computable in polynomial time
(`tf_fun_ones_unary`), so it Karp-reduces this language to the strings `y ++ y`
(`m2_ww_in_p`), and P is closed downward under Karp reductions (`m2_p_down_closed`). -/
theorem PvsNP.Units.m2_x_ones_unary_square_p :
    ({x : List Bool | ∃ y : List Bool, List.replicate (x.count true) true = y ++ y} :
      Language Bool) ∈ PvsNP.P := by
  apply PvsNP.Units.m2_p_down_closed _
    ({x : List Bool | ∃ y : List Bool, x = y ++ y} : Language Bool)
  · exact ⟨fun x : List Bool => List.replicate (x.count true) true,
      PvsNP.Units.tf_fun_ones_unary, fun _ => Iff.rfl⟩
  · exact PvsNP.Units.m2_ww_in_p
