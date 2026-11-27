import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_tseitin_and

theorem clause_true_iff (a : assgn) (C : clause) :
    evalClause a C = true ↔ ∃ l ∈ C, evalLiteral a l = true :=
  evalClause_literal_iff a C

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
      have hl2 : evalLiteral a l = true := by
        rw [← evalLiteral_congr (h l hl)]
        exact hlt
      have hx : evalClause a C = true := (clause_true_iff a C).2 ⟨l, hl, hl2⟩
      rw [hC] at hx
      exact absurd hx (by simp)
  | true =>
    have hC' : evalClause a' C = true := by
      obtain ⟨l, hl, hlt⟩ := (clause_true_iff a C).1 hC
      exact (clause_true_iff a' C).2 ⟨l, hl, by
        rw [evalLiteral_congr (h l hl)]
        exact hlt⟩
    rw [hC']

theorem mem_filter_z {a : assgn} {z v : var} (hv : v ≠ z) :
    v ∈ a.filter (fun u => u ≠ z) ↔ v ∈ a := by
  simp [List.mem_filter, hv]

theorem evalLiteral_add_z {a : assgn} {z : var} {l : literal} (hl : l.2 ≠ z) :
    evalLiteral (z :: a) l = evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  have hv : v ≠ z := hl
  by_cases hva : v ∈ a
  · have hv' : v ∈ z :: a := by simp [hva]
    simp [evalLiteral, evalVar, hva, hv']
  · have hv' : v ∉ z :: a := by simp [hva, hv]
    simp [evalLiteral, evalVar, hva, hv']

theorem mem_add_z {a : assgn} {z v : var} (hv : v ≠ z) : v ∈ z :: a ↔ v ∈ a := by
  simp [hv]

theorem sat_add_z {a : assgn} {N : cnf} {z : var} (hN : ∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z) :
    satisfiesCnf a N → satisfiesCnf (z :: a) N := by
  intro hs
  refine (evalCnf_clause_iff (z :: a) N).2 (fun C hC => ?_)
  rw [evalClause_congr (a := a) (a' := z :: a) (fun l hl => ?_)]
  · exact (evalCnf_clause_iff a N).1 hs C hC
  · exact mem_add_z (hN C hC l hl)

theorem sat_filter_z {a : assgn} {N : cnf} {z : var} (hN : ∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z) :
    satisfiesCnf a N → satisfiesCnf (a.filter (fun v => v ≠ z)) N := by
  intro hs
  refine (evalCnf_clause_iff (a.filter (fun v => v ≠ z)) N).2 (fun C hC => ?_)
  rw [evalClause_congr (a := a) (a' := a.filter (fun v => v ≠ z)) (fun l hl => ?_)]
  · exact (evalCnf_clause_iff a N).1 hs C hC
  · exact mem_filter_z (hN C hC l hl)

theorem lit_not (a : assgn) (s : Bool) (v : var) :
    evalLiteral a (!s, v) = !(evalLiteral a (s, v)) := by
  cases s <;> simp [evalLiteral]

theorem evalLiteral_neg_of_false {a : assgn} {l : literal} (h : evalLiteral a l = false) :
    evalLiteral a (!l.1, l.2) = true := by
  rw [lit_not, h]
  rfl

theorem z_not_mem_filter (a : assgn) (z : var) : z ∉ a.filter (fun v => v ≠ z) := by
  simp [List.mem_filter]

end PvsNP.Units.m3_tseitin_and

/-- A Tseitin variable for the conjunction of two literals: `z` encodes `l₁ ∧ l₂`. -/
theorem PvsNP.Units.m3_tseitin_and :
    ∀ (N : cnf) (z : var) (l₁ l₂ : literal), l₁.2 ≠ z → l₂.2 ≠ z →
      (∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z) →
      (SAT ([(false, z), l₁] :: [(false, z), l₂] ::
          [(true, z), (!l₁.1, l₁.2), (!l₂.1, l₂.2)] :: N) ↔ SAT N) := by
  intro N z l₁ l₂ h1z h2z hNz
  constructor
  · rintro ⟨a, h⟩
    obtain ⟨-, h2'⟩ := (PvsNP.Units.m3_tseitin_and.cnf_cons_iff a [(false, z), l₁] _).1 h
    obtain ⟨-, h3'⟩ := (PvsNP.Units.m3_tseitin_and.cnf_cons_iff a [(false, z), l₂] _).1 h2'
    obtain ⟨-, hN⟩ := (PvsNP.Units.m3_tseitin_and.cnf_cons_iff a
      [(true, z), (!l₁.1, l₁.2), (!l₂.1, l₂.2)] N).1 h3'
    exact ⟨a, hN⟩
  · rintro ⟨a, hN⟩
    cases hb1 : evalLiteral a l₁ with
    | true =>
      cases hb2 : evalLiteral a l₂ with
      | true =>
        refine ⟨z :: a, (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(false, z), l₁] _).2
          ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff (z :: a) [(false, z), l₁]).2
            ⟨l₁, by simp, ?_⟩, ?_⟩⟩
        · rw [PvsNP.Units.m3_tseitin_and.evalLiteral_add_z h1z]
          exact hb1
        · refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a) [(false, z), l₂] _).2
            ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff (z :: a) [(false, z), l₂]).2
              ⟨l₂, by simp, ?_⟩, ?_⟩
          · rw [PvsNP.Units.m3_tseitin_and.evalLiteral_add_z h2z]
            exact hb2
          · exact (PvsNP.Units.m3_tseitin_and.cnf_cons_iff (z :: a)
              [(true, z), (!l₁.1, l₁.2), (!l₂.1, l₂.2)] N).2
              ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff (z :: a)
                [(true, z), (!l₁.1, l₁.2), (!l₂.1, l₂.2)]).2
                ⟨(true, z), by simp, by
                  simp [PvsNP.Units.m3_tseitin_and.evalLiteral_true_var]⟩,
               PvsNP.Units.m3_tseitin_and.sat_add_z hNz hN⟩
      | false =>
        have hFa : satisfiesCnf (a.filter (fun v => v ≠ z)) N :=
          PvsNP.Units.m3_tseitin_and.sat_filter_z hNz hN
        refine ⟨a.filter (fun v => v ≠ z),
          (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(false, z), l₁] _).2
          ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff _ [(false, z), l₁]).2
            ⟨(false, z), by simp, by
              simp [evalLiteral, evalVar, PvsNP.Units.m3_tseitin_and.z_not_mem_filter]⟩, ?_⟩⟩
        refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(false, z), l₂] _).2
          ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff _ [(false, z), l₂]).2
            ⟨(false, z), by simp, by
              simp [evalLiteral, evalVar, PvsNP.Units.m3_tseitin_and.z_not_mem_filter]⟩, ?_⟩
        refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _
          [(true, z), (!l₁.1, l₁.2), (!l₂.1, l₂.2)] N).2 ⟨?_, hFa⟩
        refine (PvsNP.Units.m3_tseitin_and.clause_true_iff _
          [(true, z), (!l₁.1, l₁.2), (!l₂.1, l₂.2)]).2
          ⟨(!l₂.1, l₂.2), by simp, ?_⟩
        rw [PvsNP.Units.m3_tseitin_and.lit_not]
        rw [PvsNP.Units.m3_tseitin_and.evalLiteral_congr
          (a := a) (a' := a.filter (fun v => v ≠ z)) (l := l₂)
          (PvsNP.Units.m3_tseitin_and.mem_filter_z h2z)]
        rw [hb2]
        rfl
    | false =>
      have hFa : satisfiesCnf (a.filter (fun v => v ≠ z)) N :=
        PvsNP.Units.m3_tseitin_and.sat_filter_z hNz hN
      refine ⟨a.filter (fun v => v ≠ z),
        (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(false, z), l₁] _).2
        ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff _ [(false, z), l₁]).2
          ⟨(false, z), by simp, by
            simp [evalLiteral, evalVar, PvsNP.Units.m3_tseitin_and.z_not_mem_filter]⟩, ?_⟩⟩
      refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _ [(false, z), l₂] _).2
        ⟨(PvsNP.Units.m3_tseitin_and.clause_true_iff _ [(false, z), l₂]).2
          ⟨(false, z), by simp, by
            simp [evalLiteral, evalVar, PvsNP.Units.m3_tseitin_and.z_not_mem_filter]⟩, ?_⟩
      refine (PvsNP.Units.m3_tseitin_and.cnf_cons_iff _
        [(true, z), (!l₁.1, l₁.2), (!l₂.1, l₂.2)] N).2 ⟨?_, hFa⟩
      refine (PvsNP.Units.m3_tseitin_and.clause_true_iff _
        [(true, z), (!l₁.1, l₁.2), (!l₂.1, l₂.2)]).2
        ⟨(!l₁.1, l₁.2), by simp, ?_⟩
      have hneg : evalLiteral (a.filter (fun v => v ≠ z)) (!l₁.1, l₁.2) = true := by
        rw [PvsNP.Units.m3_tseitin_and.lit_not]
        rw [PvsNP.Units.m3_tseitin_and.evalLiteral_congr
          (a := a) (a' := a.filter (fun v => v ≠ z)) (l := l₁)
          (PvsNP.Units.m3_tseitin_and.mem_filter_z h1z)]
        rw [hb1]
        rfl
      exact hneg
