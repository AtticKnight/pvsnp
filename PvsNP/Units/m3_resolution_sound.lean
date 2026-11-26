import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_resolution_sound :
    ∀ (a : assgn) (C D : clause) (v : var),
      evalClause a ((true, v) :: C) = true → evalClause a ((false, v) :: D) = true →
        evalClause a (C ++ D) = true := by
  intro a C D v h1 h2
  simp only [evalClause, List.any_cons, List.any_append, Bool.or_eq_true] at h1 h2 ⊢
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · simp only [evalLiteral, decide_eq_true_eq] at h1 h2
      rw [h1] at h2
      exact absurd h2 (by decide)
    · exact Or.inr h2
  · exact Or.inl h1
