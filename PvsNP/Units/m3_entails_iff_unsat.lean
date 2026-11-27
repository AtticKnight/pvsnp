import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_entails_iff_unsat

/-- Flipping a literal's sign flips its value. -/
theorem neg_lit (a : assgn) (l : literal) : evalLiteral a (!l.1, l.2) = !evalLiteral a l := by
  rcases l with ⟨s, v⟩
  cases h : evalVar a v <;> cases s <;> simp [evalLiteral, h]

/-- The one-literal clauses of the negated literals of `C` all hold exactly when `C` fails. -/
theorem neg_cnf (a : assgn) (C : clause) :
    evalCnf a (C.map (fun l => [(!l.1, l.2)])) = !evalClause a C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    simp only [evalCnf, evalClause, List.map_cons, List.all_cons, List.any_cons,
      List.any_nil] at ih ⊢
    rw [ih, neg_lit]
    cases evalLiteral a l <;> simp

end PvsNP.Units.m3_entails_iff_unsat

/-- `N` entails `C` exactly when `N` with the negated literals of `C` as unit clauses is
unsatisfiable. -/
theorem PvsNP.Units.m3_entails_iff_unsat :
    ∀ (N : cnf) (C : clause),
      (∀ a : assgn, satisfiesCnf a N → evalClause a C = true) ↔
        ¬ SAT (C.map (fun l => [(!l.1, l.2)]) ++ N) := by
  intro N C
  constructor
  · rintro h ⟨a, ha⟩
    unfold satisfiesCnf at ha
    rw [evalCnf_app_iff, PvsNP.Units.m3_entails_iff_unsat.neg_cnf] at ha
    have h2 := h a ha.2
    rw [h2] at ha
    exact absurd ha.1 (by decide)
  · intro h a ha
    by_contra hc
    apply h
    refine ⟨a, ?_⟩
    unfold satisfiesCnf
    rw [evalCnf_app_iff, PvsNP.Units.m3_entails_iff_unsat.neg_cnf]
    exact ⟨by simpa using hc, ha⟩
