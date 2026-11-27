import Mathlib
import PvsNP.Defs
import PvsNP.Units.m2_p_trivial

/-- Every input represents a natural number, so Lagrange's theorem makes the
four-square language the universal language, including the empty input. -/
theorem PvsNP.Units.m2_x_sum_four_squares_p :
    ({x : List Bool | ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 =
      Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.P := by
  have allInputs :
      ({x : List Bool | ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 =
        Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Nat.sum_four_squares _
  rw [allInputs]
  exact PvsNP.Units.m2_p_trivial.2
