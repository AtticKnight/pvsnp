import Mathlib
import PvsNP.Defs
import CookLevin

/-!
# The implication graph of the two-literal clauses of a CNF is skew-symmetric

One step from `p` to `q` comes from the clause `[¬p, q]` or `[q, ¬p]` in `N`; read with
`Bool.not_not`, the same clause is a step from `¬q` to `¬p`. Induction on the
`ReflTransGen` chain reverses it. No machine is involved (vendored Cook-Levin model).
-/

set_option autoImplicit false

/-- The implication graph of the two-literal clauses of a CNF is skew-symmetric (vendored model). -/
theorem PvsNP.Units.m3_twosat_skew_symmetric :
    ∀ (N : cnf) (l m : literal),
      Relation.ReflTransGen (fun p q : literal => [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) l m →
        Relation.ReflTransGen (fun p q : literal => [(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) (!m.1, m.2) (!l.1, l.2) := by
  intro N l m h
  have step : ∀ {p q : literal},
      ([(!p.1, p.2), q] ∈ N ∨ [q, (!p.1, p.2)] ∈ N) →
      ([(!(!q.1), q.2), (!p.1, p.2)] ∈ N ∨ [(!p.1, p.2), (!(!q.1), q.2)] ∈ N) := by
    intro p q hpq
    simp only [Bool.not_not]
    rcases hpq with h | h
    · exact Or.inr h
    · exact Or.inl h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h1 h2 ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (step h2)) ih
