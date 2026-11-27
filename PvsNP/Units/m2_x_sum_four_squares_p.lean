import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_trivial

set_option autoImplicit false

namespace PvsNP.Units.m2_x_sum_four_squares_p

/-- By Lagrange's four-square theorem every natural number is a sum of four squares,
so the language is every binary string. -/
theorem lang_eq_univ :
    ({x : List Bool | ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 =
      Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) = Set.univ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact Nat.sum_four_squares _

end PvsNP.Units.m2_x_sum_four_squares_p

theorem PvsNP.Units.m2_x_sum_four_squares_p :
    ({x : List Bool | ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 =
      Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.P := by
  rw [PvsNP.Units.m2_x_sum_four_squares_p.lang_eq_univ]
  exact PvsNP.Units.m2_p_trivial.2
