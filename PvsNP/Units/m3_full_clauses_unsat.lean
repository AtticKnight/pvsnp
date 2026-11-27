import Mathlib
import PvsNP.Defs
import CookLevin

/-- A CNF holding every full clause on `n` variables is unsatisfiable: given an assignment `a`,
    the full clause with pattern `s i = !evalVar a i` is in the CNF, and each of its literals
    `(!evalVar a i, i)` is false under `a`, so `a` falsifies that clause. -/
theorem PvsNP.Units.m3_full_clauses_unsat : ∀ (n : ℕ) (N : cnf), (∀ s : Fin n → Bool, List.ofFn (fun i => (s i, (i : ℕ))) ∈ N) → ¬ SAT N := by
  intro n N hN hsat
  obtain ⟨a, ha⟩ := hsat
  have hclause := (evalCnf_clause_iff a N).mp ha _ (hN (fun i => !evalVar a (i : ℕ)))
  obtain ⟨l, hl, hev⟩ := (evalClause_literal_iff a _).mp hclause
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
  simp [evalLiteral] at hev
