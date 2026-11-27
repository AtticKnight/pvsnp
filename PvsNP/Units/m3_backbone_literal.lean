import Mathlib
import PvsNP.Defs
import CookLevin

/-- A literal whose negation is unsatisfiable beside a formula is true in
    every model of it. -/
theorem PvsNP.Units.m3_backbone_literal :
    ∀ (N : cnf) (l : literal), ¬ SAT ([(!l.1, l.2)] :: N) →
      ∀ a : assgn, satisfiesCnf a N → evalLiteral a l = true := by
  intro N l hunsat a haN
  by_contra hl
  rcases l with ⟨s, v⟩
  have hflip : evalLiteral a (!s, v) = true := by
    simp [evalLiteral] at hl ⊢
    cases s <;> cases hv : evalVar a v <;> simp_all
  have hclause : evalClause a [(!s, v)] = true := by
    simp [evalClause, List.any_cons, List.any_nil, Bool.or_false, hflip]
  exact hunsat ⟨a, by
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at haN ⊢
    exact ⟨hclause, haN⟩⟩
