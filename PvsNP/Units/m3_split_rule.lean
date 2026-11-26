import Mathlib
import PvsNP.Defs
import CookLevin

/-- Splitting on a variable preserves satisfiability: `N` is satisfiable exactly when it is
satisfiable with the unit clause `v` added, or with the unit clause `¬v` added. Left to right,
keep the satisfying assignment and pick the side by whether `v` is in it; right to left, the same
assignment satisfies `N` once the unit clause is dropped. -/
theorem PvsNP.Units.m3_split_rule :
    ∀ (N : cnf) (v : var), SAT N ↔ (SAT ([(true, v)] :: N) ∨ SAT ([(false, v)] :: N)) := by
  intro N v
  constructor
  · rintro ⟨a, ha⟩
    unfold satisfiesCnf evalCnf at ha
    by_cases hv : v ∈ a
    · left
      refine ⟨a, ?_⟩
      unfold satisfiesCnf evalCnf
      rw [List.all_cons, Bool.and_eq_true]
      exact ⟨by simp [evalClause, evalLiteral, evalVar, hv], ha⟩
    · right
      refine ⟨a, ?_⟩
      unfold satisfiesCnf evalCnf
      rw [List.all_cons, Bool.and_eq_true]
      exact ⟨by simp [evalClause, evalLiteral, evalVar, hv], ha⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩) <;> refine ⟨a, ?_⟩ <;>
      unfold satisfiesCnf evalCnf at ha ⊢ <;>
      rw [List.all_cons, Bool.and_eq_true] at ha <;>
      exact ha.2
