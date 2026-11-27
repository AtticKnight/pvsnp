import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_sat_subset_mono : ∀ N M : cnf, (∀ C ∈ M, C ∈ N) → SAT N → SAT M := by
  intro N M hsub hsat
  obtain ⟨a, ha⟩ := hsat
  refine ⟨a, ?_⟩
  simp only [satisfiesCnf, evalCnf, List.all_eq_true] at ha ⊢
  intro C hC
  exact ha C (hsub C hC)
