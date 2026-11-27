import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_self_subsuming :
    ∀ (N : cnf) (C D : clause) (v : var), (∀ l ∈ C, l ∈ D) →
      (SAT (((true, v) :: C) :: ((false, v) :: D) :: N) ↔ SAT (((true, v) :: C) :: D :: N)) := by
  intro N C D v hCD
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha ⊢
    refine ⟨ha.1, ?_, ha.2.2⟩
    simp only [evalClause, List.any_cons, Bool.or_eq_true, evalLiteral, List.any_eq_true] at ha ⊢
    cases hv : evalVar a v
    · rcases ha.1 with h1 | ⟨l, hlC, hla⟩
      · simp [hv] at h1
      · exact ⟨l, hCD l hlC, hla⟩
    · rcases ha.2.1 with h2 | ⟨l, hlD, hla⟩
      · simp [hv] at h2
      · exact ⟨l, hlD, hla⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha ⊢
    refine ⟨ha.1, ?_, ha.2.2⟩
    simp only [evalClause, List.any_cons, Bool.or_eq_true]
    exact Or.inr ha.2.1
