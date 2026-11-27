import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_consistent_literals_sat :
    ∀ N : cnf, (∀ C ∈ N, C ≠ []) →
      (∀ C ∈ N, ∀ D ∈ N, ∀ l ∈ C, (!l.1, l.2) ∉ D) → SAT N := by
  intro N hne hcons
  refine ⟨(N.flatten.filter (fun l => l.1)).map Prod.snd, ?_⟩
  simp only [satisfiesCnf, evalCnf, List.all_eq_true]
  intro C hC
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil C (hne C hC)
  simp only [evalClause, List.any_eq_true]
  refine ⟨l, hl, ?_⟩
  obtain ⟨s, v⟩ := l
  cases s
  · simp only [evalLiteral, evalVar]
    have : v ∉ (N.flatten.filter (fun l => l.1)).map Prod.snd := by
      intro hv
      obtain ⟨⟨s', v'⟩, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨hf, hs⟩ := List.mem_filter.mp hm
      obtain ⟨D, hD, hmem⟩ := List.mem_flatten.mp hf
      subst hs
      exact hcons C hC D hD _ hl hmem
    revert this
    generalize (N.flatten.filter (fun l => l.1)).map Prod.snd = a
    intro this
    simp [evalLiteral, evalVar, this]
  · simp only [evalLiteral, evalVar]
    have : v ∈ (N.flatten.filter (fun l => l.1)).map Prod.snd :=
      List.mem_map.mpr ⟨(true, v), List.mem_filter.mpr
        ⟨List.mem_flatten.mpr ⟨C, hC, hl⟩, rfl⟩, rfl⟩
    revert this
    generalize (N.flatten.filter (fun l => l.1)).map Prod.snd = a
    intro this
    simp [evalLiteral, evalVar, this]
