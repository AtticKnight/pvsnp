import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_subsumption :
    ∀ (N : cnf) (C D : clause), (∀ l ∈ C, l ∈ D) →
      (SAT (C :: D :: N) ↔ SAT (C :: N)) := by
  intro N C D hCD
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1, ha.2.2⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha ⊢
    refine ⟨ha.1, ?_, ha.2⟩
    simp only [evalClause, List.any_eq_true] at ha ⊢
    obtain ⟨l, hlC, hla⟩ := ha.1
    exact ⟨l, hCD l hlC, hla⟩
