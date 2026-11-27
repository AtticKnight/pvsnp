import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_resolution_closure_sound :
    ∀ N : cnf,
      (∀ S : Set clause, (∀ C ∈ N, C ∈ S) →
        (∀ C ∈ S, ∀ D ∈ S, ∀ v : var, (true, v) ∈ C → (false, v) ∈ D →
          C.filter (fun l => decide (l ≠ (true, v))) ++ D.filter (fun l => decide (l ≠ (false, v))) ∈ S) →
        [] ∈ S) →
      ¬ SAT N := by
  intro N hclose ⟨a, ha⟩
  rw [satisfiesCnf, evalCnf_clause_iff] at ha
  have hempty : evalClause a [] = true := by
    apply hclose {C : clause | evalClause a C = true}
    · intro C hC
      exact ha C hC
    · intro C hC D hD v _ _
      change evalClause a C = true at hC
      change evalClause a D = true at hD
      show evalClause a (C.filter (fun l => decide (l ≠ (true, v))) ++
        D.filter (fun l => decide (l ≠ (false, v)))) = true
      rw [evalClause_literal_iff] at hC hD ⊢
      cases hv : evalVar a v with
      | true =>
        obtain ⟨l, hlD, hle⟩ := hD
        refine ⟨l, List.mem_append_right _ (List.mem_filter.mpr ⟨hlD, ?_⟩), hle⟩
        simp only [decide_eq_true_eq]
        intro heq
        subst heq
        simp [evalLiteral, hv] at hle
      | false =>
        obtain ⟨l, hlC, hle⟩ := hC
        refine ⟨l, List.mem_append_left _ (List.mem_filter.mpr ⟨hlC, ?_⟩), hle⟩
        simp only [decide_eq_true_eq]
        intro heq
        subst heq
        simp [evalLiteral, hv] at hle
  simp [evalClause] at hempty
