import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_sat_iff_literal_choice :
    ∀ N : cnf, SAT N ↔
      ∃ f : clause → literal, (∀ C ∈ N, f C ∈ C) ∧
        ∀ C ∈ N, ∀ D ∈ N, f D ≠ (!(f C).1, (f C).2) := by
  intro N
  classical
  constructor
  · rintro ⟨a, ha⟩
    have hall : ∀ C ∈ N, ∃ l ∈ C, evalLiteral a l = true := by
      intro C hC
      have hcl : evalClause a C = true := (evalCnf_clause_iff a N).mp ha C hC
      exact (evalClause_literal_iff a C).mp hcl
    let f : clause → literal := fun C =>
      if h : ∃ l ∈ C, evalLiteral a l = true then Classical.choose h else (false, 0)
    have hf_spec : ∀ C ∈ N, f C ∈ C ∧ evalLiteral a (f C) = true := by
      intro C hC
      have hex := hall C hC
      have hfc : f C = Classical.choose hex := dif_pos hex
      rw [hfc]
      exact Classical.choose_spec hex
    refine ⟨f, fun C hC => (hf_spec C hC).1, ?_⟩
    intro C hC D hD heq
    have h1 := (hf_spec C hC).2
    have h2 := (hf_spec D hD).2
    rw [heq] at h2
    rcases hfC : f C with ⟨s, v⟩
    rw [hfC] at h1 h2
    simp only [evalLiteral, evalVar] at h1 h2
    cases s <;> by_cases hv : v ∈ a <;> simp_all
  · rintro ⟨f, hmem, hnoopp⟩
    let a : assgn := ((N.map f).filter (fun l => l.1)).map Prod.snd
    refine ⟨a, (evalCnf_clause_iff a N).mpr ?_⟩
    intro C hC
    refine (evalClause_literal_iff a C).mpr ⟨f C, hmem C hC, ?_⟩
    cases hfC : f C with
    | mk s v =>
      simp only [evalLiteral, evalVar]
      cases s with
      | true =>
        have hv : v ∈ a := by
          simp only [a, List.mem_map, List.mem_filter]
          exact ⟨(true, v), ⟨⟨C, hC, hfC⟩, rfl⟩, rfl⟩
        simp [hv]
      | false =>
        have hv : v ∉ a := by
          intro hvin
          simp only [a, List.mem_map, List.mem_filter] at hvin
          obtain ⟨⟨s', v'⟩, ⟨⟨D, hD, hfD⟩, hs'⟩, hv'⟩ := hvin
          simp only at hs' hv'
          subst hs' hv'
          have hopp := hnoopp C hC D hD
          rw [hfC, hfD] at hopp
          exact hopp rfl
        simp [hv]
