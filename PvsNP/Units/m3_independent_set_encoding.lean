import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_independent_set_encoding :
    ∀ (E : List (var × var)) (a : assgn),
      satisfiesCnf a (E.map (fun e => [(false, e.1), (false, e.2)])) ↔ ∀ e ∈ E, ¬ (e.1 ∈ a ∧ e.2 ∈ a) := by
  intro E a
  simp only [satisfiesCnf, evalCnf, List.all_eq_true]
  constructor
  · intro h e he ⟨h1, h2⟩
    have hcl := h _ (List.mem_map_of_mem he)
    simp [evalClause, evalLiteral, evalVar, h1, h2] at hcl
  · intro h C hC
    rcases List.mem_map.mp hC with ⟨e, he, rfl⟩
    by_cases h1 : e.1 ∈ a
    · have h2 : e.2 ∉ a := fun h2 => h e he ⟨h1, h2⟩
      simp [evalClause, evalLiteral, evalVar, h2]
    · simp [evalClause, evalLiteral, evalVar, h1]
