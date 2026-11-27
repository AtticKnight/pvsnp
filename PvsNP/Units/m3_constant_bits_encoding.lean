import Mathlib
import PvsNP.Defs
import CookLevin

/-- Unit clauses fix a block of `m` variables to the binary digits of a number (vendored model). -/
theorem PvsNP.Units.m3_constant_bits_encoding :
    ∀ (a : assgn) (k x m : ℕ),
      satisfiesCnf a ((List.range m).map (fun j => [(Nat.testBit k j, x + j)])) ↔
        ∀ j < m, (x + j ∈ a ↔ Nat.testBit k j = true) := by
  intro a k x m
  simp only [satisfiesCnf, evalCnf, List.all_eq_true, List.mem_map, List.mem_range]
  constructor
  · intro h j hj
    have h1 := h [(Nat.testBit k j, x + j)] ⟨j, hj, rfl⟩
    by_cases hmem : x + j ∈ a <;> cases hb : Nat.testBit k j <;>
      simp [evalClause, evalLiteral, evalVar, hmem, hb] at h1 ⊢
  · rintro h _ ⟨j, hj, rfl⟩
    have h1 := h j hj
    by_cases hmem : x + j ∈ a <;> cases hb : Nat.testBit k j <;>
      simp [evalClause, evalLiteral, evalVar, hmem, hb] at h1 ⊢
