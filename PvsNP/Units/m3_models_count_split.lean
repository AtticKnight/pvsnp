import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_models_count_split

/-- The opposite literal evaluates to the negation of the literal. -/
theorem evalLiteral_neg (a : assgn) (s : Bool) (v : var) :
    evalLiteral a (!s, v) = !evalLiteral a (s, v) := by
  show decide (evalVar a v = !s) = !decide (evalVar a v = s)
  cases h : evalVar a v <;> cases s <;> rfl

/-- Splitting the models of `N` on the value of the literal `(s, v)`: the models
where the literal holds plus the models where its opposite holds are exactly
the models of `N`. Proved by induction on the list of assignments. -/
theorem count_split (n : ℕ) (N : cnf) (s : Bool) (v : var) :
    ∀ L : List assgn,
      (L.filter (fun a => evalCnf a ([(s, v)] :: N))).length +
          (L.filter (fun a => evalCnf a ([(!s, v)] :: N))).length =
        (L.filter (fun a => evalCnf a N)).length := by
  intro L
  induction L with
  | nil => rfl
  | cons a L ih =>
    have hP : evalCnf a ([(s, v)] :: N) = (evalLiteral a (s, v) && evalCnf a N) := by
      simp [evalCnf, evalClause]
    have hQ : evalCnf a ([(!s, v)] :: N) = (!evalLiteral a (s, v) && evalCnf a N) := by
      simp [evalCnf, evalClause, evalLiteral_neg]
    rw [List.filter_cons, List.filter_cons, List.filter_cons, hP, hQ]
    cases h1 : evalLiteral a (s, v) <;> cases h2 : evalCnf a N <;> simp [ih] <;> omega

end PvsNP.Units.m3_models_count_split

/-- Splitting on a literal partitions the models (counting Davis-Putnam,
vendored model). -/
theorem PvsNP.Units.m3_models_count_split :
    ∀ (n : ℕ) (N : cnf) (l : literal),
      ((List.range n).sublists.filter (fun a => evalCnf a ([l] :: N))).length +
          ((List.range n).sublists.filter (fun a => evalCnf a ([(!l.1, l.2)] :: N))).length =
        ((List.range n).sublists.filter (fun a => evalCnf a N)).length := by
  intro n N l
  obtain ⟨s, v⟩ := l
  exact PvsNP.Units.m3_models_count_split.count_split n N s v (List.range n).sublists
