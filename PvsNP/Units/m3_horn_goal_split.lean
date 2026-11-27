import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_horn_goal_split : ∀ N : cnf, (∀ C ∈ N, (C.filter (fun l => l.1)).length ≤ 1) →
  (SAT N ↔ ∀ C ∈ N, (∀ l ∈ C, l.1 = false) → SAT (C :: N.filter (fun D => decide (∃ l ∈ D, l.1 = true)))) := by
  intro N hH
  constructor
  · rintro ⟨a, ha⟩ C hC _
    have ha' := (evalCnf_clause_iff a N).mp ha
    refine ⟨a, ?_⟩
    apply (evalCnf_clause_iff a _).mpr
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD'
    · exact ha' _ hC
    · exact ha' D (List.mem_filter.mp hD').1
  · intro h
    classical
    have hDmem : ∀ D : clause, D ∈ N.filter (fun D => decide (∃ l ∈ D, l.1 = true)) ↔
        D ∈ N ∧ ∃ l ∈ D, l.1 = true := by
      intro D
      simp only [List.mem_filter, decide_eq_true_eq]
    obtain ⟨M, hM⟩ : ∃ M : assgn, ∀ v : var, v ∈ M ↔
        (∃ C ∈ N, ∃ l ∈ C, l.2 = v) ∧
          ∀ b : assgn, satisfiesCnf b (N.filter (fun D => decide (∃ l ∈ D, l.1 = true))) → v ∈ b := by
      refine ⟨(N.flatMap (fun C => C.map (fun l => l.2))).filter
        (fun v => decide (∀ b : assgn,
          satisfiesCnf b (N.filter (fun D => decide (∃ l ∈ D, l.1 = true))) → v ∈ b)), ?_⟩
      intro v
      simp only [List.mem_filter, List.mem_flatMap, List.mem_map, decide_eq_true_eq]
    refine ⟨M, ?_⟩
    apply (evalCnf_clause_iff M N).mpr
    intro C hC
    by_cases hn : ∀ l ∈ C, l.1 = false
    · obtain ⟨a, ha⟩ := h C hC hn
      have ha' := (evalCnf_clause_iff a _).mp ha
      have haD : satisfiesCnf a (N.filter (fun D => decide (∃ l ∈ D, l.1 = true))) :=
        (evalCnf_clause_iff a _).mpr (fun D hD => ha' D (List.mem_cons_of_mem _ hD))
      obtain ⟨l, hl, ht⟩ := (evalClause_literal_iff a C).mp (ha' C List.mem_cons_self)
      rcases l with ⟨s, w⟩
      have hs := hn _ hl
      simp only at hs
      subst hs
      have hwa : w ∉ a := by
        intro c
        simp [evalLiteral, evalVar, c] at ht
      have hwM : w ∉ M := fun c => hwa (((hM w).mp c).2 a haD)
      exact (evalClause_literal_iff _ _).mpr ⟨(false, w), hl, by simp [evalLiteral, evalVar, hwM]⟩
    · obtain ⟨l, hl'⟩ := not_forall.mp hn
      obtain ⟨hl, hpos⟩ := Classical.not_imp.mp hl'
      rcases l with ⟨s, u⟩
      have hs : s = true := by simpa using hpos
      subst hs
      have hCD : C ∈ N.filter (fun D => decide (∃ l ∈ D, l.1 = true)) :=
        (hDmem C).mpr ⟨hC, (true, u), hl, rfl⟩
      by_cases hall : ∀ m ∈ C, m.1 = false → m.2 ∈ M
      · have huM : u ∈ M := by
          refine (hM u).mpr ⟨⟨C, hC, (true, u), hl, rfl⟩, fun b hb => ?_⟩
          have hbC := (evalCnf_clause_iff b _).mp hb C hCD
          obtain ⟨m, hm, ht⟩ := (evalClause_literal_iff b C).mp hbC
          rcases m with ⟨s, x⟩
          cases s
          · exfalso
            have hxb : x ∈ b := ((hM x).mp (hall (false, x) hm rfl)).2 b hb
            simp [evalLiteral, evalVar, hxb] at ht
          · have h1 : (true, x) ∈ C.filter (fun l => l.1) := List.mem_filter.mpr ⟨hm, rfl⟩
            have h2 : (true, u) ∈ C.filter (fun l => l.1) := List.mem_filter.mpr ⟨hl, rfl⟩
            have hlen : (C.filter (fun l => l.1)).length = 1 := by
              have hp := List.length_pos_of_mem h1
              have hq := hH C hC
              omega
            obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hlen
            rw [hy, List.mem_singleton] at h1 h2
            have e : (true, x) = (true, u) := h1.trans h2.symm
            have e' : x = u := (Prod.mk.inj e).2
            have hxb : x ∈ b := by simpa [evalLiteral, evalVar] using ht
            rw [← e']
            exact hxb
        exact (evalClause_literal_iff _ _).mpr ⟨(true, u), hl, by simp [evalLiteral, evalVar, huM]⟩
      · obtain ⟨m, hm'⟩ := not_forall.mp hall
        obtain ⟨hm, hm''⟩ := Classical.not_imp.mp hm'
        obtain ⟨hmf, hmM⟩ := Classical.not_imp.mp hm''
        rcases m with ⟨s, x⟩
        simp only at hmf hmM
        subst hmf
        exact (evalClause_literal_iff _ _).mpr ⟨(false, x), hm, by simp [evalLiteral, evalVar, hmM]⟩
