import Mathlib
import PvsNP.Defs
import CookLevin

/-
Closes m3_full_adder_sum_encoding: the eight 4-clauses enforce
`s ↔ x ⊕ y ⊕ z` on every assignment `a`. Verified directly over all 16
membership truth combinations for `x, y, z, s ∈ a`.
-/

set_option autoImplicit false

/-- Eight clauses define the sum bit of a full adder, `s ↔ x ⊕ y ⊕ z` (vendored model). -/
theorem PvsNP.Units.m3_full_adder_sum_encoding :
    ∀ (a : assgn) (x y z s : var),
      satisfiesCnf a [[(false, x), (true, y), (true, z), (true, s)], [(true, x), (false, y), (true, z), (true, s)],
          [(true, x), (true, y), (false, z), (true, s)], [(false, x), (false, y), (false, z), (true, s)],
          [(true, x), (true, y), (true, z), (false, s)], [(false, x), (false, y), (true, z), (false, s)],
          [(false, x), (true, y), (false, z), (false, s)], [(true, x), (false, y), (false, z), (false, s)]] ↔
        decide (s ∈ a) = xor (xor (decide (x ∈ a)) (decide (y ∈ a))) (decide (z ∈ a)) := by
  intro a x y z s
  by_cases hx : x ∈ a <;> by_cases hy : y ∈ a <;> by_cases hz : z ∈ a <;> by_cases hs : s ∈ a <;>
    (simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar, hx, hy, hz, hs]; try decide)
