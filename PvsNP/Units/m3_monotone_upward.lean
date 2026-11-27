import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_monotone_upward :
    ∀ (N : cnf) (a b : assgn), (∀ C ∈ N, ∀ l ∈ C, l.1 = true) →
      satisfiesCnf a N → (∀ v ∈ a, v ∈ b) → satisfiesCnf b N := by
  intro N a b hpos ha hsub
  refine (evalCnf_clause_iff _ _).mpr ?_
  intro C hC
  have haC := (evalCnf_clause_iff a N).mp ha C hC
  obtain ⟨⟨s, v⟩, hlC, hla⟩ := (evalClause_literal_iff a C).mp haC
  have hs : s = true := hpos C hC (s, v) hlC
  subst hs
  have hva : v ∈ a := by
    by_contra hv
    simp [evalLiteral, evalVar, hv] at hla
  have hvb : v ∈ b := hsub v hva
  refine (evalClause_literal_iff b C).mpr ⟨(true, v), hlC, ?_⟩
  simp [evalLiteral, evalVar, hvb]
