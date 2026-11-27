import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_naesat_fresh_var :
    ∀ (N : cnf) (z : var), (∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z) →
      (SAT N ↔ ∃ a : assgn, ∀ C ∈ N.map (fun D => (true, z) :: D),
        C.any (evalLiteral a) = true ∧ C.any (fun l => !evalLiteral a l) = true) := by
  intro N z hfresh
  constructor
  · rintro ⟨a, ha⟩
    have hall := (evalCnf_clause_iff a N).mp ha
    let a' : assgn := a.filter (fun v => v ≠ z)
    refine ⟨a', ?_⟩
    intro C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    constructor
    · obtain ⟨⟨s, v⟩, hlv, hlit⟩ := (evalClause_literal_iff a D).mp (hall D hD)
      rw [List.any_eq_true]
      refine ⟨(s, v), List.mem_cons_of_mem _ hlv, ?_⟩
      have hv : v ≠ z := hfresh D hD (s, v) hlv
      have hvar : evalVar a' v = evalVar a v := by simp [a', evalVar, hv]
      simp only [evalLiteral, hvar]
      exact hlit
    · rw [List.any_eq_true]
      refine ⟨(true, z), List.mem_cons_self, ?_⟩
      simp [a', evalLiteral, evalVar]
  · rintro ⟨a, ha⟩
    by_cases hz : z ∈ a
    · let a' : assgn := (N.flatten.map Prod.snd).filter (fun v => v ∉ a)
      refine ⟨a', (evalCnf_clause_iff a' N).mpr ?_⟩
      intro D hD
      have h2 := (ha ((true, z) :: D) (List.mem_map.mpr ⟨D, hD, rfl⟩)).2
      rw [List.any_cons] at h2
      have hzt : (!evalLiteral a (true, z)) = false := by
        simp [evalLiteral, evalVar, hz]
      rw [hzt, Bool.false_or, List.any_eq_true] at h2
      obtain ⟨⟨s, v⟩, hlv, hlit⟩ := h2
      rw [evalClause_literal_iff]
      refine ⟨(s, v), hlv, ?_⟩
      have hvN : v ∈ N.flatten.map Prod.snd :=
        List.mem_map.mpr ⟨(s, v), List.mem_flatten.mpr ⟨D, hD, hlv⟩, rfl⟩
      have hflip : evalVar a' v = !evalVar a v := by
        by_cases hva : v ∈ a
        · simp only [a', evalVar, List.mem_filter, hvN, true_and, hva,
            not_true_eq_false, decide_false, decide_true, Bool.not_true]
          rfl
        · simp only [a', evalVar, List.mem_filter, hvN, true_and, hva,
            not_false_eq_true, decide_true, decide_false, Bool.not_false]
      cases s <;> cases hvv : evalVar a v <;> simp [evalLiteral, hflip, hvv] at hlit ⊢
    · refine ⟨a, (evalCnf_clause_iff a N).mpr ?_⟩
      intro D hD
      have h1 := (ha ((true, z) :: D) (List.mem_map.mpr ⟨D, hD, rfl⟩)).1
      rw [List.any_cons] at h1
      have hzf : evalLiteral a (true, z) = false := by
        simp [evalLiteral, evalVar, hz]
      rw [hzf, Bool.false_or] at h1
      exact h1
