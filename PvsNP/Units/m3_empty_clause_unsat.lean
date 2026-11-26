import Mathlib
import PvsNP.Defs
import CookLevin

open CookLevin CookLevin.Lang EvalCnfCmd CnfWellFormed

/-- A CNF with the empty clause is unsatisfiable: any satisfying assignment would have
    to make every clause true, but the empty clause has no literal to make true. -/
theorem PvsNP.Units.m3_empty_clause_unsat : ∀ N : cnf, [] ∈ N → ¬ SAT N := by
  intro N hN hsat
  obtain ⟨a, ha⟩ := hsat
  have hclause : evalClause a [] = true := (evalCnf_clause_iff a N).mp ha [] hN
  have hempty : evalClause a [] = false := rfl
  rw [hempty] at hclause
  exact Bool.noConfusion hclause
