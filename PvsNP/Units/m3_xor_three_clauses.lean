import Mathlib
import PvsNP.Defs
import CookLevin

open CookLevin

namespace PvsNP.Units.m3_xor_three_clauses

/-- The unit's statement: unfold the evaluation and case on the three memberships.
Each of the four clauses is false at exactly one point, and the four points are
those of even parity, so the CNF holds exactly at the points of odd parity. -/
theorem main (a : assgn) (x y z : var) :
    satisfiesCnf a [[(true, x), (true, y), (true, z)], [(false, x), (false, y), (true, z)],
        [(false, x), (true, y), (false, z)], [(true, x), (false, y), (false, z)]] ↔
      xor (xor (decide (x ∈ a)) (decide (y ∈ a))) (decide (z ∈ a)) = true := by
  cases h1 : decide (x ∈ a) <;> cases h2 : decide (y ∈ a) <;> cases h3 : decide (z ∈ a) <;>
    simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar, h1, h2, h3]

end PvsNP.Units.m3_xor_three_clauses

/-- Four clauses of width three say that x ⊕ y ⊕ z = 1 (vendored model). -/
theorem PvsNP.Units.m3_xor_three_clauses :
    ∀ (a : assgn) (x y z : var),
      satisfiesCnf a [[(true, x), (true, y), (true, z)], [(false, x), (false, y), (true, z)],
          [(false, x), (true, y), (false, z)], [(true, x), (false, y), (false, z)]] ↔
        xor (xor (decide (x ∈ a)) (decide (y ∈ a))) (decide (z ∈ a)) = true :=
  PvsNP.Units.m3_xor_three_clauses.main
