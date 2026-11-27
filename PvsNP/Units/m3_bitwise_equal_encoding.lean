import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_bitwise_equal_encoding :
    ∀ (a : assgn) (x y m : ℕ),
      satisfiesCnf a ((List.range m).flatMap (fun j => [[(false, x + j), (true, y + j)], [(true, x + j), (false, y + j)]])) ↔
        ∀ j < m, (x + j ∈ a ↔ y + j ∈ a) := by
  intro a x y m
  simp only [satisfiesCnf, evalCnf, List.all_eq_true, List.mem_flatMap, List.mem_range]
  constructor
  · intro h j hj
    have h1 := h [(false, x + j), (true, y + j)] ⟨j, hj, by simp⟩
    have h2 := h [(true, x + j), (false, y + j)] ⟨j, hj, by simp⟩
    by_cases hx : x + j ∈ a <;> by_cases hy : y + j ∈ a <;>
      simp_all [evalClause, evalLiteral, evalVar]
  · intro h C hC
    rcases hC with ⟨j, hj, hmem⟩
    have hij := h j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;>
      by_cases hx : x + j ∈ a <;> by_cases hy : y + j ∈ a <;>
        simp_all [evalClause, evalLiteral, evalVar]
