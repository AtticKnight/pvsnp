import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_dual_horn_greatest_model : ∀ N : cnf, (∀ C ∈ N, (C.filter (fun l => !l.1)).length ≤ 1) → SAT N →
  ∃ a : assgn, satisfiesCnf a N ∧ ∀ b : assgn, satisfiesCnf b N → ∀ v ∈ b, (∃ C ∈ N, ∃ l ∈ C, l.2 = v) → v ∈ a := by
  intro N hH hsat
  classical
  obtain ⟨b0, hb0⟩ := hsat
  obtain ⟨A, hA⟩ : ∃ A : assgn, ∀ v : var, v ∈ A ↔
      (∃ C ∈ N, ∃ l ∈ C, l.2 = v) ∧ ∃ b : assgn, satisfiesCnf b N ∧ v ∈ b := by
    refine ⟨(N.flatMap (fun C => C.map (fun l => l.2))).filter
      (fun v => decide (∃ b : assgn, satisfiesCnf b N ∧ v ∈ b)), ?_⟩
    intro v
    simp only [List.mem_filter, List.mem_flatMap, List.mem_map, decide_eq_true_eq]
  refine ⟨A, ?_, ?_⟩
  · apply (evalCnf_clause_iff A N).mpr
    intro C hC
    have pos : ∀ b : assgn, satisfiesCnf b N → ∀ u : var, (true, u) ∈ C → u ∈ b →
        evalClause A C = true := by
      intro b hb u hu hub
      have huA : u ∈ A := (hA u).mpr ⟨⟨C, hC, (true, u), hu, rfl⟩, b, hb, hub⟩
      exact (evalClause_literal_iff _ _).mpr ⟨(true, u), hu, by simp [evalLiteral, evalVar, huA]⟩
    by_cases hneg : ∃ w : var, (false, w) ∈ C
    · obtain ⟨w, hw⟩ := hneg
      by_cases hwA : w ∈ A
      · obtain ⟨_, b, hb, hwb⟩ := (hA w).mp hwA
        have hbC := (evalCnf_clause_iff b N).mp hb C hC
        obtain ⟨l, hl, ht⟩ := (evalClause_literal_iff b C).mp hbC
        rcases l with ⟨s, u⟩
        cases s
        · exfalso
          have h1 : (false, u) ∈ C.filter (fun l => !l.1) := List.mem_filter.mpr ⟨hl, rfl⟩
          have h2 : (false, w) ∈ C.filter (fun l => !l.1) := List.mem_filter.mpr ⟨hw, rfl⟩
          have hlen : (C.filter (fun l => !l.1)).length = 1 := by
            have hp := List.length_pos_of_mem h1
            have hq := hH C hC
            omega
          obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hlen
          rw [hy, List.mem_singleton] at h1 h2
          have e : (false, u) = (false, w) := h1.trans h2.symm
          have e' : u = w := (Prod.mk.inj e).2
          rw [e'] at ht
          simp [evalLiteral, evalVar, hwb] at ht
        · have hub : u ∈ b := by simpa [evalLiteral, evalVar] using ht
          exact pos b hb u hl hub
      · exact (evalClause_literal_iff _ _).mpr ⟨(false, w), hw, by simp [evalLiteral, evalVar, hwA]⟩
    · have hbC := (evalCnf_clause_iff b0 N).mp hb0 C hC
      obtain ⟨l, hl, ht⟩ := (evalClause_literal_iff b0 C).mp hbC
      rcases l with ⟨s, u⟩
      cases s
      · exact absurd ⟨u, hl⟩ hneg
      · have hub : u ∈ b0 := by simpa [evalLiteral, evalVar] using ht
        exact pos b0 hb0 u hl hub
  · intro b hb v hv hocc
    exact (hA v).mpr ⟨hocc, b, hb, hv⟩
