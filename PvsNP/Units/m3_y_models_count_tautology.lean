import Mathlib
import PvsNP.Defs
import CookLevin

open SAT_inNP

/-- A clause containing both `v` and `¬v` is satisfied by every assignment:
whichever way `v` is set, one of the two literals is true. Prepending such
a tautology to a CNF therefore does not change which assignments satisfy
it, and in particular does not change the number of models below `n`. -/
theorem PvsNP.Units.m3_y_models_count_tautology :
    ∀ (n : ℕ) (N : cnf) (C : clause) (v : var), (true, v) ∈ C → (false, v) ∈ C →
      ((List.range n).sublists.filter (fun a => evalCnf a (C :: N))).length =
        ((List.range n).sublists.filter (fun a => evalCnf a N)).length := by
  intro n N C v hpos hneg
  have hclause : ∀ a : assgn, evalClause a C = true := by
    intro a
    rw [evalClause_literal_iff]
    by_cases hv : v ∈ a
    · refine ⟨(true, v), hpos, ?_⟩
      simp only [evalLiteral, evalVar, decide_eq_true hv, decide_eq_true_eq, eq_self_iff_true]
    · refine ⟨(false, v), hneg, ?_⟩
      simp only [evalLiteral, evalVar, decide_eq_false_iff_not.mpr hv, decide_eq_true_eq,
        eq_self_iff_true]
  have hcnf : ∀ a : assgn, evalCnf a (C :: N) = evalCnf a N := by
    intro a
    show (C :: N).all (evalClause a) = N.all (evalClause a)
    rw [List.all_cons, hclause a, Bool.true_and]
  simp only [hcnf]
