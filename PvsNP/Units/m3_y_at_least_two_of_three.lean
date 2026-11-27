import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_y_at_least_two_of_three :
    ∀ (a : assgn) (x y z : var),
      satisfiesCnf a [[(true, x), (true, y)], [(true, x), (true, z)], [(true, y), (true, z)]] ↔
        (x ∈ a ∧ y ∈ a) ∨ (x ∈ a ∧ z ∈ a) ∨ (y ∈ a ∧ z ∈ a) := by
  intro a x y z
  simp only [satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.or_false,
    Bool.and_true]
  by_cases hx : x ∈ a <;> by_cases hy : y ∈ a <;> by_cases hz : z ∈ a <;> simp [hx, hy, hz]
