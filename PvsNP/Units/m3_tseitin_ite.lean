import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_tseitin_and

set_option autoImplicit false

namespace PvsNP.Units.m3_tseitin_ite

/-- Negating the sign of a literal negates its value. -/
theorem evalLiteral_not_fst {a : assgn} {c : literal} :
    evalLiteral a (!c.1, c.2) = !evalLiteral a c :=
  PvsNP.Units.m3_tseitin_and.lit_not a c.1 c.2

end PvsNP.Units.m3_tseitin_ite

/-- Defining a fresh variable as an if-then-else of literals preserves satisfiability (Tseitin, vendored model). -/
theorem PvsNP.Units.m3_tseitin_ite :
    ∀ (N : cnf) (z : var) (c l₁ l₂ : literal), c.2 ≠ z → l₁.2 ≠ z → l₂.2 ≠ z →
      (∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z) →
      (SAT ([(false, z), (!c.1, c.2), l₁] :: [(false, z), c, l₂] ::
          [(true, z), (!c.1, c.2), (!l₁.1, l₁.2)] :: [(true, z), c, (!l₂.1, l₂.2)] :: N) ↔ SAT N) := by
  intro N z c l₁ l₂ hcz h1z h2z hNz
  constructor
  · rintro ⟨a, h⟩
    obtain ⟨-, h2'⟩ := (PvsNP.Units.m3_tseitin_and.cnf_cons_iff a [(false, z), (!c.1, c.2), l₁] _).1 h
    obtain ⟨-, h3'⟩ := (PvsNP.Units.m3_tseitin_and.cnf_cons_iff a [(false, z), c, l₂] _).1 h2'
    obtain ⟨-, h4'⟩ := (PvsNP.Units.m3_tseitin_and.cnf_cons_iff a [(true, z), (!c.1, c.2), (!l₁.1, l₁.2)] _).1 h3'
    obtain ⟨-, hN⟩ := (PvsNP.Units.m3_tseitin_and.cnf_cons_iff a [(true, z), c, (!l₂.1, l₂.2)] N).1 h4'
    exact ⟨a, hN⟩
  · rintro ⟨a, hN⟩
    cases hbc : evalLiteral a c with
    | true =>
      cases hb1 : evalLiteral a l₁ with
      | true =>
        refine ⟨z :: a, (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(false, z), (!c.1, c.2), l₁] _).2 ⟨?_, ?_⟩⟩
        · exact (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2
            ⟨l₁, by simp, by rw [PvsNP.Units.m3_tseitin_and.evalLiteral_add_z h1z]; exact hb1⟩
        · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(false, z), c, l₂] _).2 ⟨?_, ?_⟩
          · exact (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2
              ⟨c, by simp, by rw [PvsNP.Units.m3_tseitin_and.evalLiteral_add_z hcz]; exact hbc⟩
          · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(true, z), (!c.1, c.2), (!l₁.1, l₁.2)] _).2 ⟨?_, ?_⟩
            · exact (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2
                ⟨(true, z), by simp, by simp [PvsNP.Units.m3_tseitin_and.evalLiteral_true_var]⟩
            · exact (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(true, z), c, (!l₂.1, l₂.2)] N).2
                ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2
                  ⟨(true, z), by simp, by simp [PvsNP.Units.m3_tseitin_and.evalLiteral_true_var]⟩,
                 PvsNP.Units.m3_tseitin_and.sat_add_z hNz hN⟩
      | false =>
        have hFa : satisfiesCnf (a.filter (fun v => v ≠ z)) N :=
          PvsNP.Units.m3_tseitin_and.sat_filter_z hNz hN
        refine ⟨a.filter (fun v => v ≠ z),
          (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(false, z), (!c.1, c.2), l₁] _).2 ⟨?_, ?_⟩⟩
        · exact (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2
            ⟨(false, z), by simp, by simp [evalLiteral, evalVar, PvsNP.Units.m3_tseitin_and.z_not_mem_filter]⟩
        · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(false, z), c, l₂] _).2 ⟨?_, ?_⟩
          · exact (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2
              ⟨(false, z), by simp, by simp [evalLiteral, evalVar, PvsNP.Units.m3_tseitin_and.z_not_mem_filter]⟩
          · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(true, z), (!c.1, c.2), (!l₁.1, l₁.2)] _).2 ⟨?_, ?_⟩
            · refine (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2 ⟨(!l₁.1, l₁.2), by simp, ?_⟩
              rw [PvsNP.Units.m3_tseitin_ite.evalLiteral_not_fst]
              rw [PvsNP.Units.m3_tseitin_and.evalLiteral_congr
                (a := a) (a' := a.filter (fun v => v ≠ z)) (l := l₁)
                (PvsNP.Units.m3_tseitin_and.mem_filter_z h1z)]
              rw [hb1]
              rfl
            · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(true, z), c, (!l₂.1, l₂.2)] N).2 ⟨?_, hFa⟩
              refine (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2 ⟨c, by simp, ?_⟩
              rw [PvsNP.Units.m3_tseitin_and.evalLiteral_congr
                (a := a) (a' := a.filter (fun v => v ≠ z)) (l := c)
                (PvsNP.Units.m3_tseitin_and.mem_filter_z hcz)]
              exact hbc
    | false =>
      cases hb2 : evalLiteral a l₂ with
      | true =>
        refine ⟨z :: a, (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(false, z), (!c.1, c.2), l₁] _).2 ⟨?_, ?_⟩⟩
        · refine (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2 ⟨(!c.1, c.2), by simp, ?_⟩
          rw [PvsNP.Units.m3_tseitin_ite.evalLiteral_not_fst]
          rw [PvsNP.Units.m3_tseitin_and.evalLiteral_add_z hcz]
          rw [hbc]
          rfl
        · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(false, z), c, l₂] _).2 ⟨?_, ?_⟩
          · exact (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2
              ⟨l₂, by simp, by rw [PvsNP.Units.m3_tseitin_and.evalLiteral_add_z h2z]; exact hb2⟩
          · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(true, z), (!c.1, c.2), (!l₁.1, l₁.2)] _).2 ⟨?_, ?_⟩
            · exact (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2
                ⟨(true, z), by simp, by simp [PvsNP.Units.m3_tseitin_and.evalLiteral_true_var]⟩
            · exact (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(true, z), c, (!l₂.1, l₂.2)] N).2
                ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2
                  ⟨(true, z), by simp, by simp [PvsNP.Units.m3_tseitin_and.evalLiteral_true_var]⟩,
                 PvsNP.Units.m3_tseitin_and.sat_add_z hNz hN⟩
      | false =>
        have hFa : satisfiesCnf (a.filter (fun v => v ≠ z)) N :=
          PvsNP.Units.m3_tseitin_and.sat_filter_z hNz hN
        refine ⟨a.filter (fun v => v ≠ z),
          (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(false, z), (!c.1, c.2), l₁] _).2 ⟨?_, ?_⟩⟩
        · exact (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2
            ⟨(false, z), by simp, by simp [evalLiteral, evalVar, PvsNP.Units.m3_tseitin_and.z_not_mem_filter]⟩
        · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(false, z), c, l₂] _).2 ⟨?_, ?_⟩
          · exact (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2
              ⟨(false, z), by simp, by simp [evalLiteral, evalVar, PvsNP.Units.m3_tseitin_and.z_not_mem_filter]⟩
          · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(true, z), (!c.1, c.2), (!l₁.1, l₁.2)] _).2 ⟨?_, ?_⟩
            · refine (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2 ⟨(!c.1, c.2), by simp, ?_⟩
              rw [PvsNP.Units.m3_tseitin_ite.evalLiteral_not_fst]
              rw [PvsNP.Units.m3_tseitin_and.evalLiteral_congr
                (a := a) (a' := a.filter (fun v => v ≠ z)) (l := c)
                (PvsNP.Units.m3_tseitin_and.mem_filter_z hcz)]
              rw [hbc]
              rfl
            · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(true, z), c, (!l₂.1, l₂.2)] N).2 ⟨?_, hFa⟩
              refine (PvsNP.Units.m3_tseitin_and.clause_true_iff _ _).2 ⟨(!l₂.1, l₂.2), by simp, ?_⟩
              rw [PvsNP.Units.m3_tseitin_and.lit_not]
              rw [PvsNP.Units.m3_tseitin_and.evalLiteral_congr
                (a := a) (a' := a.filter (fun v => v ≠ z)) (l := l₂)
                (PvsNP.Units.m3_tseitin_and.mem_filter_z h2z)]
              rw [hb2]
              rfl
