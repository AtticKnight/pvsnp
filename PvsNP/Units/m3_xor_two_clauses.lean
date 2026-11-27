import Mathlib
import PvsNP.Defs
import CookLevin

/-- The two clauses `(x ∨ y)` and `(¬x ∨ ¬y)` say that `x` and `y` differ (vendored model). -/
theorem PvsNP.Units.m3_xor_two_clauses :
    ∀ (a : assgn) (x y : var),
      satisfiesCnf a [[(true, x), (true, y)], [(false, x), (false, y)]] ↔
        decide (x ∈ a) ≠ decide (y ∈ a) := by
  intro a x y
  by_cases hx : x ∈ a <;> by_cases hy : y ∈ a <;>
    simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar, hx, hy]
