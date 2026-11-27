import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_tseitin_and

/-
Closes m3_tseitin_or: defining a fresh variable `z` as `l₁ ∨ l₂` preserves
satisfiability. Reuses the assignment-update and clause-evaluation lemmas
from settled `PvsNP.Units.m3_tseitin_and`.
-/

set_option autoImplicit false

/-- A Tseitin variable for the disjunction of two literals: `z` encodes `l₁ ∨ l₂`. -/
theorem PvsNP.Units.m3_tseitin_or :
    ∀ (N : cnf) (z : var) (l₁ l₂ : literal), l₁.2 ≠ z → l₂.2 ≠ z →
      (∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z) →
      (SAT ([(false, z), l₁, l₂] :: [(true, z), (!l₁.1, l₁.2)] ::
          [(true, z), (!l₂.1, l₂.2)] :: N) ↔ SAT N) := by
  intro N z l₁ l₂ h1z h2z hNz
  constructor
  · rintro ⟨a, h⟩
    obtain ⟨-, h2'⟩ := (PvsNP.Units.m3_tseitin_and.cnf_cons_iff a [(false, z), l₁, l₂] _).1 h
    obtain ⟨-, h3'⟩ := (PvsNP.Units.m3_tseitin_and.cnf_cons_iff a [(true, z), (!l₁.1, l₁.2)] _).1 h2'
    obtain ⟨-, hN⟩ := (PvsNP.Units.m3_tseitin_and.cnf_cons_iff a [(true, z), (!l₂.1, l₂.2)] N).1 h3'
    exact ⟨a, hN⟩
  · rintro ⟨a, hN⟩
    cases hb1 : evalLiteral a l₁ with
    | true =>
      refine ⟨z :: a,
        (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(false, z), l₁, l₂] _).2
        ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff (z :: a) [(false, z), l₁, l₂]).2
          ⟨l₁, by simp, ?_⟩, ?_⟩⟩
      · rw [PvsNP.Units.m3_tseitin_and.evalLiteral_add_z h1z]
        exact hb1
      · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(true, z), (!l₁.1, l₁.2)] _).2
          ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff (z :: a) [(true, z), (!l₁.1, l₁.2)]).2
            ⟨(true, z), by simp, by simp [PvsNP.Units.m3_tseitin_and.evalLiteral_true_var]⟩, ?_⟩
        exact (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(true, z), (!l₂.1, l₂.2)] N).2
          ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff (z :: a) [(true, z), (!l₂.1, l₂.2)]).2
            ⟨(true, z), by simp, by simp [PvsNP.Units.m3_tseitin_and.evalLiteral_true_var]⟩,
           PvsNP.Units.m3_tseitin_and.sat_add_z hNz hN⟩
    | false =>
      cases hb2 : evalLiteral a l₂ with
      | true =>
        refine ⟨z :: a,
          (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(false, z), l₁, l₂] _).2
          ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff (z :: a) [(false, z), l₁, l₂]).2
            ⟨l₂, by simp, ?_⟩, ?_⟩⟩
        · rw [PvsNP.Units.m3_tseitin_and.evalLiteral_add_z h2z]
          exact hb2
        · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(true, z), (!l₁.1, l₁.2)] _).2
            ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff (z :: a) [(true, z), (!l₁.1, l₁.2)]).2
              ⟨(true, z), by simp, by simp [PvsNP.Units.m3_tseitin_and.evalLiteral_true_var]⟩, ?_⟩
          exact (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(true, z), (!l₂.1, l₂.2)] N).2
            ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff (z :: a) [(true, z), (!l₂.1, l₂.2)]).2
              ⟨(true, z), by simp, by simp [PvsNP.Units.m3_tseitin_and.evalLiteral_true_var]⟩,
             PvsNP.Units.m3_tseitin_and.sat_add_z hNz hN⟩
      | false =>
        have hFa : satisfiesCnf (a.filter (fun v => v ≠ z)) N :=
          PvsNP.Units.m3_tseitin_and.sat_filter_z hNz hN
        refine ⟨a.filter (fun v => v ≠ z),
          (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(false, z), l₁, l₂] _).2
          ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff _ [(false, z), l₁, l₂]).2
            ⟨(false, z), by simp, by
              simp [evalLiteral, evalVar, PvsNP.Units.m3_tseitin_and.z_not_mem_filter]⟩, ?_⟩⟩
        refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(true, z), (!l₁.1, l₁.2)] _).2
          ⟨?_, ?_⟩
        · refine (PvsNP.Units.m3_tseitin_and.clause_true_iff _ [(true, z), (!l₁.1, l₁.2)]).2
            ⟨(!l₁.1, l₁.2), by simp, ?_⟩
          rw [PvsNP.Units.m3_tseitin_and.lit_not]
          rw [PvsNP.Units.m3_tseitin_and.evalLiteral_congr
            (a := a) (a' := a.filter (fun v => v ≠ z)) (l := l₁)
            (PvsNP.Units.m3_tseitin_and.mem_filter_z h1z)]
          rw [hb1]
          rfl
        · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(true, z), (!l₂.1, l₂.2)] N).2
            ⟨?_, hFa⟩
          refine (PvsNP.Units.m3_tseitin_and.clause_true_iff _ [(true, z), (!l₂.1, l₂.2)]).2
            ⟨(!l₂.1, l₂.2), by simp, ?_⟩
          rw [PvsNP.Units.m3_tseitin_and.lit_not]
          rw [PvsNP.Units.m3_tseitin_and.evalLiteral_congr
            (a := a) (a' := a.filter (fun v => v ≠ z)) (l := l₂)
            (PvsNP.Units.m3_tseitin_and.mem_filter_z h2z)]
          rw [hb2]
          rfl
