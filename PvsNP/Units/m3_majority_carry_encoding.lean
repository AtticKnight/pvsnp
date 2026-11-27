import Mathlib
import PvsNP.Defs
import CookLevin

open SAT_inNP

/-- Six clauses define the carry of a full adder: the first three force the
carry when any two inputs are true, the last three forbid it when any two
inputs are false, so the carry holds exactly for the majority. -/
theorem PvsNP.Units.m3_majority_carry_encoding :
    ∀ (a : assgn) (x y z c : var),
      satisfiesCnf a [[(false, x), (false, y), (true, c)], [(false, x), (false, z), (true, c)], [(false, y), (false, z), (true, c)],
          [(true, x), (true, y), (false, c)], [(true, x), (true, z), (false, c)], [(true, y), (true, z), (false, c)]] ↔
        (c ∈ a ↔ (x ∈ a ∧ y ∈ a) ∨ (x ∈ a ∧ z ∈ a) ∨ (y ∈ a ∧ z ∈ a)) := by
  intro a x y z c
  by_cases hx : x ∈ a <;> by_cases hy : y ∈ a <;> by_cases hz : z ∈ a <;> by_cases hc : c ∈ a <;>
    simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar, hx, hy, hz, hc]
