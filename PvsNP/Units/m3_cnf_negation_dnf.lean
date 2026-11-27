import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_cnf_negation_dnf

theorem lit (a : assgn) (l : literal) : evalLiteral a (!l.1, l.2) = !evalLiteral a l := by
  rcases l with ⟨s, v⟩
  simp only [evalLiteral]
  cases evalVar a v <;> cases s <;> rfl

theorem cl (a : assgn) : ∀ C : clause,
    (!evalClause a C) = C.all (fun l => evalLiteral a (!l.1, l.2))
  | [] => by simp [evalClause]
  | l :: C => by
    have ih := cl a C
    simp only [evalClause] at ih
    simp only [evalClause, List.any_cons, List.all_cons, lit, Bool.not_or, ih]

end PvsNP.Units.m3_cnf_negation_dnf

theorem PvsNP.Units.m3_cnf_negation_dnf : ∀ (a : assgn) (N : cnf),
  (!evalCnf a N) = N.any (fun C => C.all (fun l => evalLiteral a (!l.1, l.2))) := by
  intro a N
  induction N with
  | nil => simp [evalCnf]
  | cons C N ih =>
    simp only [evalCnf] at ih
    simp only [evalCnf, List.all_cons, List.any_cons, Bool.not_and, ih,
      PvsNP.Units.m3_cnf_negation_dnf.cl]
