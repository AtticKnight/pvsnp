import Mathlib
import PvsNP.Defs
import CookLevin

/-- A satisfiable CNF has a satisfying assignment that uses only its own variables:
    filter the satisfying assignment down to the variables occurring in `N`; no literal
    of `N` changes its value, since every variable of a literal of `N` survives the
    filter. -/
theorem PvsNP.Units.m3_sat_vars_restrict :
    ∀ N : cnf, SAT N →
      ∃ a : assgn, (∀ v ∈ a, ∃ C ∈ N, ∃ s : Bool, (s, v) ∈ C) ∧ satisfiesCnf a N := by
  intro N hsat
  obtain ⟨a₀, ha₀⟩ := hsat
  refine ⟨a₀.filter (fun v => v ∈ SAT_inNP.varsOfCnf N), ?_, ?_⟩
  · -- Every variable of the filtered assignment occurs in some clause of `N`.
    intro v hv
    have hvN : v ∈ SAT_inNP.varsOfCnf N := by
      have h := (List.mem_filter.mp hv).2
      simpa using h
    rw [SAT_inNP.varsOfCnf, List.mem_flatten] at hvN
    obtain ⟨lvs, hlvs, hvl⟩ := hvN
    rw [List.mem_map] at hlvs
    obtain ⟨C, hC, rfl⟩ := hlvs
    rw [SAT_inNP.varsOfClause, List.mem_flatten] at hvl
    obtain ⟨lv, hlv, hvl2⟩ := hvl
    rw [List.mem_map] at hlv
    obtain ⟨l, hl, rfl⟩ := hlv
    rw [SAT_inNP.varsOfLiteral, List.mem_singleton] at hvl2
    refine ⟨C, hC, l.1, ?_⟩
    rw [hvl2]
    exact hl
  · -- The filtered assignment still satisfies `N`.
    have ha₀' : ∀ C ∈ N, evalClause a₀ C = true := (evalCnf_clause_iff a₀ N).mp ha₀
    rw [satisfiesCnf, evalCnf_clause_iff]
    intro C hC
    obtain ⟨l, hl, hlit⟩ := (evalClause_literal_iff a₀ C).mp (ha₀' C hC)
    rw [evalClause, List.any_eq_true]
    refine ⟨l, hl, ?_⟩
    obtain ⟨s, v⟩ := l
    have hvN : v ∈ SAT_inNP.varsOfCnf N := SAT_inNP.varsOfCnf_mem N C (s, v) hC hl
    have hvar : evalVar (a₀.filter (fun v => v ∈ SAT_inNP.varsOfCnf N)) v = evalVar a₀ v := by
      simp only [evalVar, List.mem_filter, hvN, decide_true, and_true]
    simp only [evalLiteral, hvar]
    exact hlit
