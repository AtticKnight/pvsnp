import Mathlib
import PvsNP.Defs
import CookLevin

/-- The clauses `(¬x ∨ y)` and `(x ∨ ¬y)` hold exactly when `x` and `y` are equal (vendored model). -/
theorem PvsNP.Units.m3_equivalence_clauses :
    ∀ (a : assgn) (x y : var),
      satisfiesCnf a [[(false, x), (true, y)], [(true, x), (false, y)]] ↔ (x ∈ a ↔ y ∈ a) := by
  intro a x y
  by_cases hx : x ∈ a <;> by_cases hy : y ∈ a <;>
    simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar, hx, hy]
