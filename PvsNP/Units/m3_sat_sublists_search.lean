import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_sat_sublists_search :
    ∀ N : cnf, SAT N ↔ ∃ a ∈ (N.flatten.map Prod.snd).sublists, satisfiesCnf a N := by
  intro N
  constructor
  · rintro ⟨a₀, ha₀⟩
    refine ⟨(N.flatten.map Prod.snd).filter (fun v => v ∈ a₀),
      List.mem_sublists.mpr List.filter_sublist, ?_⟩
    have ha₀' : ∀ C ∈ N, evalClause a₀ C = true := (evalCnf_clause_iff a₀ N).mp ha₀
    rw [satisfiesCnf, evalCnf_clause_iff]
    intro C hC
    obtain ⟨l, hl, hlit⟩ := (evalClause_literal_iff a₀ C).mp (ha₀' C hC)
    rw [evalClause, List.any_eq_true]
    refine ⟨l, hl, ?_⟩
    obtain ⟨s, v⟩ := l
    have hvN : v ∈ N.flatten.map Prod.snd :=
      List.mem_map.mpr ⟨(s, v), List.mem_flatten.mpr ⟨C, hC, hl⟩, rfl⟩
    have hvar : evalVar ((N.flatten.map Prod.snd).filter (fun v => v ∈ a₀)) v = evalVar a₀ v := by
      simp only [evalVar, List.mem_filter, hvN, true_and, decide_eq_true_eq]
    simp only [evalLiteral, hvar]
    exact hlit
  · rintro ⟨a, _, ha⟩
    exact ⟨a, ha⟩
