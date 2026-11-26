import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_positive_clause_sat :
    ∀ N : cnf, (∀ C ∈ N, ∃ v : var, (true, v) ∈ C) → SAT N := by
  intro N hN
  refine ⟨N.flatten.map Prod.snd, ?_⟩
  simp only [satisfiesCnf, evalCnf, List.all_eq_true]
  intro C hC
  obtain ⟨v, hv⟩ := hN C hC
  simp only [evalClause, List.any_eq_true]
  refine ⟨(true, v), hv, ?_⟩
  have hmem : v ∈ N.flatten.map Prod.snd :=
    List.mem_map.mpr ⟨(true, v), List.mem_flatten.mpr ⟨C, hC, hv⟩, rfl⟩
  simp only [evalLiteral, evalVar, hmem, decide_true]
