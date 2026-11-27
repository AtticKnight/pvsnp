import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_unit_resolution_sound :
    ∀ (a : assgn) (l : literal) (C : clause),
      evalClause a [l] = true → evalClause a ((!l.1, l.2) :: C) = true → evalClause a C = true := by
  intro a l C h1 h2
  obtain ⟨s, v⟩ := l
  simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at h1 h2 ⊢
  rcases h2 with h2 | h2
  · simp only [evalLiteral, decide_eq_true_eq] at h1 h2
    rw [h1] at h2
    cases s <;> exact absurd h2 (by decide)
  · exact h2
