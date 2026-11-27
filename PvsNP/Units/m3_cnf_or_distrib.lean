import Mathlib
import PvsNP.Defs
import CookLevin

/-
Desk unit `m3_cnf_or_distrib` (campaign `pvsnp`, mission 3: CNF encodings in the vendored
Cook-Levin model, `vendor/CookLevin/CookLevin/SAT/SAT.lean`: `cnf`, `clause`, `literal`, `assgn`,
`evalLiteral`, `evalClause`, `evalCnf`, used as they stand).

The clause-wise product of two CNFs `N₁` and `N₂`, the list of the clauses `C ++ D` for `C` in `N₁`
and `D` in `N₂`, has under every assignment the value of `N₁` or the value of `N₂`.

Proof. By the vendored `evalCnf_clause_iff` and `evalClause_literal_iff` both sides become
statements about members: a clause `C ++ D` is true exactly when `C` or `D` is, the clauses of the
product are exactly the `C ++ D`, and "every pair has `C` or `D` true" holds exactly when every `C`
is true or every `D` is. The proofs are new; no upstream or campaign file is copied.
-/

set_option autoImplicit false

namespace PvsNP.Units.m3_cnf_or_distrib

/-- A concatenated clause is true exactly when one of its two parts is. -/
theorem clause_append_true_iff (a : assgn) (C D : clause) :
    evalClause a (C ++ D) = true ↔ evalClause a C = true ∨ evalClause a D = true := by
  rw [evalClause_literal_iff, evalClause_literal_iff, evalClause_literal_iff]
  constructor
  · rintro ⟨l, hl, hla⟩
    rcases List.mem_append.mp hl with h | h
    · exact Or.inl ⟨l, h, hla⟩
    · exact Or.inr ⟨l, h, hla⟩
  · rintro (⟨l, hl, hla⟩ | ⟨l, hl, hla⟩)
    · exact ⟨l, List.mem_append.mpr (Or.inl hl), hla⟩
    · exact ⟨l, List.mem_append.mpr (Or.inr hl), hla⟩

/-- The clauses of the clause-wise product are exactly the `C ++ D` with `C` in the first formula
and `D` in the second. -/
theorem mem_clauseProduct_iff (N₁ N₂ : cnf) (E : clause) :
    E ∈ N₁.flatMap (fun C => N₂.map (fun D => C ++ D)) ↔
      ∃ C, C ∈ N₁ ∧ ∃ D, D ∈ N₂ ∧ C ++ D = E := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨C, hC, hE⟩
    obtain ⟨D, hD, hCD⟩ := List.mem_map.mp hE
    exact ⟨C, hC, D, hD, hCD⟩
  · rintro ⟨C, hC, D, hD, hCD⟩
    exact ⟨C, hC, List.mem_map.mpr ⟨D, hD, hCD⟩⟩

/-- The clause-wise product of two CNFs is true exactly when one of the two is. -/
theorem evalCnf_clauseProduct_iff (a : assgn) (N₁ N₂ : cnf) :
    evalCnf a (N₁.flatMap (fun C => N₂.map (fun D => C ++ D))) = true ↔
      evalCnf a N₁ = true ∨ evalCnf a N₂ = true := by
  rw [evalCnf_clause_iff, evalCnf_clause_iff, evalCnf_clause_iff]
  constructor
  · intro h
    by_cases h₁ : ∀ C, C ∈ N₁ → evalClause a C = true
    · exact Or.inl h₁
    · refine Or.inr (fun D hD => ?_)
      by_contra hDf
      apply h₁
      intro C hC
      have hCD : evalClause a (C ++ D) = true :=
        h (C ++ D) ((mem_clauseProduct_iff N₁ N₂ (C ++ D)).mpr ⟨C, hC, D, hD, rfl⟩)
      rcases (clause_append_true_iff a C D).mp hCD with hC' | hD'
      · exact hC'
      · exact absurd hD' hDf
  · rintro (h | h) E hE
    · obtain ⟨C, hC, D, _, hCD⟩ := (mem_clauseProduct_iff N₁ N₂ E).mp hE
      rw [← hCD]
      exact (clause_append_true_iff a C D).mpr (Or.inl (h C hC))
    · obtain ⟨C, _, D, hD, hCD⟩ := (mem_clauseProduct_iff N₁ N₂ E).mp hE
      rw [← hCD]
      exact (clause_append_true_iff a C D).mpr (Or.inr (h D hD))

/-- The posted statement: the two Booleans are equal because each is true exactly when the other
is. -/
theorem evalCnf_clauseProduct (a : assgn) (N₁ N₂ : cnf) :
    evalCnf a (N₁.flatMap (fun C => N₂.map (fun D => C ++ D))) =
      (evalCnf a N₁ || evalCnf a N₂) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true]
  exact evalCnf_clauseProduct_iff a N₁ N₂

end PvsNP.Units.m3_cnf_or_distrib

theorem PvsNP.Units.m3_cnf_or_distrib : ∀ (a : assgn) (N₁ N₂ : cnf),
  evalCnf a (N₁.flatMap (fun C => N₂.map (fun D => C ++ D))) = (evalCnf a N₁ || evalCnf a N₂) :=
  fun a N₁ N₂ => PvsNP.Units.m3_cnf_or_distrib.evalCnf_clauseProduct a N₁ N₂
