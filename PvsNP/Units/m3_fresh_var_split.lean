import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_fresh_var_split

theorem clause_true_iff (a : assgn) (C : clause) :
    evalClause a C = true ↔ ∃ l ∈ C, evalLiteral a l = true :=
  evalClause_literal_iff a C

theorem clause_cons_true (a : assgn) (l : literal) (C : clause) :
    evalClause a (l :: C) = true ↔ evalLiteral a l = true ∨ evalClause a C = true := by
  rw [clause_true_iff, clause_true_iff]
  constructor
  · rintro ⟨m, hm, hmt⟩
    rcases List.mem_cons.1 hm with rfl | hm
    · exact Or.inl hmt
    · exact Or.inr ⟨m, hm, hmt⟩
  · rintro (h | ⟨m, hm, hmt⟩)
    · exact ⟨l, List.mem_cons_self, h⟩
    · exact ⟨m, List.mem_cons.2 (Or.inr hm), hmt⟩

theorem clause_append_true (a : assgn) (C D : clause) :
    evalClause a (C ++ D) = true ↔ evalClause a C = true ∨ evalClause a D = true := by
  rw [clause_true_iff, clause_true_iff, clause_true_iff]
  constructor
  · rintro ⟨l, hl, hlt⟩
    rcases List.mem_append.1 hl with hl | hl
    · exact Or.inl ⟨l, hl, hlt⟩
    · exact Or.inr ⟨l, hl, hlt⟩
  · rintro (⟨l, hl, hlt⟩ | ⟨l, hl, hlt⟩)
    · exact ⟨l, List.mem_append.2 (Or.inl hl), hlt⟩
    · exact ⟨l, List.mem_append.2 (Or.inr hl), hlt⟩

theorem cnf_cons_iff (a : assgn) (C : clause) (N : cnf) :
    satisfiesCnf a (C :: N) ↔ evalClause a C = true ∧ satisfiesCnf a N := by
  constructor
  · intro h
    have h' := (evalCnf_clause_iff a (C :: N)).1 h
    exact ⟨h' C (by simp), (evalCnf_clause_iff a N).2 (fun D hD => h' D (by simp [hD]))⟩
  · rintro ⟨hC, hN⟩
    exact (evalCnf_clause_iff a (C :: N)).2 (by
      intro D hD
      rcases List.mem_cons.1 hD with rfl | hD
      · exact hC
      · exact (evalCnf_clause_iff a N).1 hN D hD)

theorem evalLiteral_true_var {a : assgn} {z : var} :
    evalLiteral a (true, z) = true ↔ z ∈ a := by
  simp [evalLiteral, evalVar]

theorem evalLiteral_false_var {a : assgn} {z : var} :
    evalLiteral a (false, z) = true ↔ z ∉ a := by
  simp [evalLiteral, evalVar]

theorem evalLiteral_add_z {a : assgn} {z : var} {l : literal} (hl : l.2 ≠ z) :
    evalLiteral (z :: a) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  by_cases hva : v ∈ a
  · have hv' : v ∈ z :: a := by simp [hva]
    simp [evalLiteral, evalVar, hva, hv']
  · have hv' : v ∉ z :: a := by simp [hva, hv]
    simp [evalLiteral, evalVar, hva, hv']

theorem evalClause_add_z (a : assgn) (z : var) (C : clause) (hC : ∀ l ∈ C, l.2 ≠ z) :
    evalClause (z :: a) C = evalClause a C := by
  cases h : evalClause a C with
  | false =>
    cases h' : evalClause (z :: a) C with
    | false => rfl
    | true =>
      obtain ⟨l, hl, hlt⟩ := (clause_true_iff (z :: a) C).1 h'
      have hl2 : evalLiteral a l = true := by
        rw [← evalLiteral_add_z (hC l hl)]
        exact hlt
      have : evalClause a C = true := (clause_true_iff a C).2 ⟨l, hl, hl2⟩
      rw [h] at this
      exact absurd this (by simp)
  | true =>
    have h' : evalClause (z :: a) C = true := by
      obtain ⟨l, hl, hlt⟩ := (clause_true_iff a C).1 h
      exact (clause_true_iff (z :: a) C).2 ⟨l, hl, by
        rw [evalLiteral_add_z (hC l hl)]
        exact hlt⟩
    rw [h']

theorem sat_no_z {a a' : assgn} {N : cnf} {z : var} (hN : ∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z)
    (hagree : ∀ l : literal, l.2 ≠ z → evalLiteral a' l = evalLiteral a l) :
    satisfiesCnf a N → satisfiesCnf a' N := by
  intro hs
  refine (evalCnf_clause_iff a' N).2 (fun C hC => ?_)
  obtain ⟨l, hl, hlt⟩ := (clause_true_iff a C).1 ((evalCnf_clause_iff a N).1 hs C hC)
  exact (clause_true_iff a' C).2 ⟨l, hl, by rw [hagree l (hN C hC l hl)]; exact hlt⟩


theorem evalLiteral_congr {a a' : assgn} {l : literal} (h : l.2 ∈ a' ↔ l.2 ∈ a) :
    evalLiteral a' l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  by_cases hv : v ∈ a
  · have hv' : v ∈ a' := h.2 hv
    simp [evalLiteral, evalVar, hv, hv']
  · have hv' : v ∉ a' := fun hc => hv (h.1 hc)
    simp [evalLiteral, evalVar, hv, hv']

theorem evalClause_congr {a a' : assgn} {C : clause} (h : ∀ l ∈ C, l.2 ∈ a' ↔ l.2 ∈ a) :
    evalClause a' C = evalClause a C := by
  cases hC : evalClause a C with
  | false =>
    cases hC' : evalClause a' C with
    | false => rfl
    | true =>
      obtain ⟨l, hl, hlt⟩ := (clause_true_iff a' C).1 hC'
      have : evalLiteral a l = true := by
        rw [← evalLiteral_congr (h l hl)]
        exact hlt
      have : evalClause a C = true := (clause_true_iff a C).2 ⟨l, hl, this⟩
      rw [hC] at this
      exact absurd this (by simp)
  | true =>
    have hC' : evalClause a' C = true := by
      obtain ⟨l, hl, hlt⟩ := (clause_true_iff a C).1 hC
      exact (clause_true_iff a' C).2 ⟨l, hl, by
        rw [evalLiteral_congr (h l hl)]
        exact hlt⟩
    rw [hC']

theorem sat_erase_z {a : assgn} {N : cnf} {z : var} (hN : ∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z) :
    satisfiesCnf a N → satisfiesCnf (a.filter (fun v => v ≠ z)) N := by
  intro hs
  refine (evalCnf_clause_iff (a.filter (fun v => v ≠ z)) N).2 (fun C hC => ?_)
  rw [evalClause_congr (a := a) (a' := a.filter (fun v => v ≠ z)) (fun l hl => ?_)]
  · exact (evalCnf_clause_iff a N).1 hs C hC
  · exact by simp [List.mem_filter, hN C hC l hl]

end PvsNP.Units.m3_fresh_var_split

/-- A fresh variable `z` splits a clause into two clauses: `((true, z) :: C)` and
    `((false, z) :: D)` are jointly satisfiable exactly when `C ++ D` is. -/
theorem PvsNP.Units.m3_fresh_var_split :
    ∀ (N : cnf) (C D : clause) (z : var),
      (∀ E ∈ (C ++ D) :: N, ∀ l ∈ E, l.2 ≠ z) →
      (SAT (((true, z) :: C) :: ((false, z) :: D) :: N) ↔ SAT ((C ++ D) :: N)) := by
  intro N C D z hz
  have hCz : ∀ l ∈ C, l.2 ≠ z := fun l hl =>
    hz (C ++ D) (List.mem_cons.2 (Or.inl rfl)) l (List.mem_append.2 (Or.inl hl))
  have hDz : ∀ l ∈ D, l.2 ≠ z := fun l hl =>
    hz (C ++ D) (List.mem_cons.2 (Or.inl rfl)) l (List.mem_append.2 (Or.inr hl))
  have hNz : ∀ E ∈ N, ∀ l ∈ E, l.2 ≠ z := fun E hE l hl =>
    hz E (List.mem_cons.2 (Or.inr hE)) l hl
  have hCDz : ∀ l ∈ C ++ D, l.2 ≠ z := by
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact hCz l hl
    · exact hDz l hl
  constructor
  · rintro ⟨a, h⟩
    obtain ⟨h1, h2'⟩ := (PvsNP.Units.m3_fresh_var_split.cnf_cons_iff a ((true, z) :: C) _).1 h
    obtain ⟨h2, hN⟩ := (PvsNP.Units.m3_fresh_var_split.cnf_cons_iff a ((false, z) :: D) N).1 h2'
    refine ⟨a, (PvsNP.Units.m3_fresh_var_split.cnf_cons_iff a (C ++ D) N).2 ⟨?_, hN⟩⟩
    rcases (PvsNP.Units.m3_fresh_var_split.clause_cons_true a (true, z) C).1 h1 with ht | hC
    · have hza : z ∈ a := (PvsNP.Units.m3_fresh_var_split.evalLiteral_true_var).1 ht
      rcases (PvsNP.Units.m3_fresh_var_split.clause_cons_true a (false, z) D).1 h2 with hf | hD
      · have hznot : z ∉ a := (PvsNP.Units.m3_fresh_var_split.evalLiteral_false_var).1 hf
        exact absurd hza hznot
      · exact (PvsNP.Units.m3_fresh_var_split.clause_append_true a C D).2 (Or.inr hD)
    · exact (PvsNP.Units.m3_fresh_var_split.clause_append_true a C D).2 (Or.inl hC)
  · rintro ⟨a, h⟩
    obtain ⟨hCD, hN⟩ := (PvsNP.Units.m3_fresh_var_split.cnf_cons_iff a (C ++ D) N).1 h
    rcases (PvsNP.Units.m3_fresh_var_split.clause_append_true a C D).1 hCD with hC | hD
    · have hCa : evalClause (a.filter (fun v => v ≠ z)) C = true := by
        rw [PvsNP.Units.m3_fresh_var_split.evalClause_congr (a := a) (a' := a.filter (fun v => v ≠ z))
          (fun l hl => by simp [List.mem_filter, hCz l hl])]
        exact hC
      have hNa : satisfiesCnf (a.filter (fun v => v ≠ z)) N :=
        PvsNP.Units.m3_fresh_var_split.sat_erase_z hNz hN
      refine ⟨a.filter (fun v => v ≠ z), (PvsNP.Units.m3_fresh_var_split.cnf_cons_iff (a.filter (fun v => v ≠ z)) ((true, z) :: C) _).2
        ⟨(PvsNP.Units.m3_fresh_var_split.clause_cons_true (a.filter (fun v => v ≠ z)) (true, z) C).2 (Or.inr hCa), ?_⟩⟩
      exact (PvsNP.Units.m3_fresh_var_split.cnf_cons_iff (a.filter (fun v => v ≠ z)) ((false, z) :: D) N).2
        ⟨(PvsNP.Units.m3_fresh_var_split.clause_cons_true (a.filter (fun v => v ≠ z)) (false, z) D).2
          (Or.inl (by
            simp [PvsNP.Units.m3_fresh_var_split.evalLiteral_false_var, List.mem_filter, and_comm])), hNa⟩
    · have hDa : evalClause (z :: a) D = true := by
        rw [PvsNP.Units.m3_fresh_var_split.evalClause_add_z a z D hDz]
        exact hD
      have hNa : satisfiesCnf (z :: a) N :=
        PvsNP.Units.m3_fresh_var_split.sat_no_z hNz
          (fun l hl => PvsNP.Units.m3_fresh_var_split.evalLiteral_add_z hl) hN
      refine ⟨z :: a, (PvsNP.Units.m3_fresh_var_split.cnf_cons_iff (z :: a) ((true, z) :: C) _).2
        ⟨(PvsNP.Units.m3_fresh_var_split.clause_cons_true (z :: a) (true, z) C).2
          (Or.inl (by simp [PvsNP.Units.m3_fresh_var_split.evalLiteral_true_var])), ?_⟩⟩
      exact (PvsNP.Units.m3_fresh_var_split.cnf_cons_iff (z :: a) ((false, z) :: D) N).2
        ⟨(PvsNP.Units.m3_fresh_var_split.clause_cons_true (z :: a) (false, z) D).2
          (Or.inr hDa), hNa⟩
