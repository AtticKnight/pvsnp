import Mathlib
import PvsNP.Defs
import CookLevin

/-- Removing repeated clauses keeps satisfiability (vendored model). -/
theorem PvsNP.Units.m3_sat_dedup : ∀ N : cnf, SAT N.dedup ↔ SAT N := by
  intro N
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_eq_true] at ha ⊢
    intro C hC
    exact ha C (List.mem_dedup.mpr hC)
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_eq_true] at ha ⊢
    intro C hC
    exact ha C (List.mem_dedup.mp hC)
