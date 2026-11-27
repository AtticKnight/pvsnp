import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_palindrome_in_p
import PvsNP.Units.m2_ww_in_p
import PvsNP.Units.m2_p_inter

/-!
Original short proof. The posted language is the intersection of the
palindrome language (settled unit `m2_palindrome_in_p`) and the language of
strings written twice (settled unit `m2_ww_in_p`), so it is in `P` by
closure of `P` under intersection (settled unit `m2_p_inter`).

This proves only the posted statement in PvsNP.Defs.
-/

namespace PvsNP.Units.m2_x_pal_and_square_p

theorem inter_eq :
    ({x : List Bool | x.reverse = x ∧ ∃ y : List Bool, x = y ++ y} : Language Bool) =
      ({x : List Bool | x.reverse = x} : Language Bool) ⊓
        ({x : List Bool | ∃ y : List Bool, x = y ++ y} : Language Bool) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]

end PvsNP.Units.m2_x_pal_and_square_p

/-- The palindromes that are one string written twice are in P (TM2). -/
theorem PvsNP.Units.m2_x_pal_and_square_p :
    ({x : List Bool | x.reverse = x ∧ ∃ y : List Bool, x = y ++ y} : Language Bool) ∈ PvsNP.P := by
  rw [PvsNP.Units.m2_x_pal_and_square_p.inter_eq]
  exact PvsNP.Units.m2_p_inter _ _ PvsNP.Units.m2_palindrome_in_p PvsNP.Units.m2_ww_in_p
