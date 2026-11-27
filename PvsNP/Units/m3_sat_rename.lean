import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_sat_rename :
    ∀ (N : cnf) (f : var → var), Function.Injective f →
      (SAT (N.map (fun C => C.map (fun l => (l.1, f l.2)))) ↔ SAT N) := by
  intro N f hf
  constructor
  · rintro ⟨a, ha⟩
    let a' : assgn := (N.flatten.map Prod.snd).filter (fun v => decide (f v ∈ a))
    refine ⟨a', ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_eq_true] at ha ⊢
    intro C hC
    have hC' := ha (C.map (fun l => (l.1, f l.2))) (List.mem_map.mpr ⟨C, hC, rfl⟩)
    simp only [evalClause, List.any_eq_true] at hC' ⊢
    obtain ⟨l', hl', hev⟩ := hC'
    obtain ⟨⟨s, v⟩, hmem, rfl⟩ := List.mem_map.mp hl'
    refine ⟨(s, v), hmem, ?_⟩
    have hvN : v ∈ N.flatten.map Prod.snd :=
      List.mem_map.mpr ⟨(s, v), List.mem_flatten.mpr ⟨C, hC, hmem⟩, rfl⟩
    have hiff : v ∈ a' ↔ f v ∈ a := by
      simp only [a', List.mem_filter, decide_eq_true_eq, hvN, true_and]
    simp only [evalLiteral, evalVar] at hev ⊢
    by_cases h : f v ∈ a
    · have h' : v ∈ a' := hiff.mpr h
      simpa [h, h'] using hev
    · have h' : v ∉ a' := fun hc => h (hiff.mp hc)
      simpa [h, h'] using hev
  · rintro ⟨a, ha⟩
    refine ⟨a.map f, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_eq_true] at ha ⊢
    intro C' hC'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
    have hCa := ha C hC
    simp only [evalClause, List.any_eq_true] at hCa ⊢
    obtain ⟨⟨s, v⟩, hmem, hev⟩ := hCa
    refine ⟨(s, f v), List.mem_map.mpr ⟨(s, v), hmem, rfl⟩, ?_⟩
    have hiff : f v ∈ a.map f ↔ v ∈ a := by
      simp only [List.mem_map, hf.eq_iff, exists_eq_right]
    simp only [evalLiteral, evalVar] at hev ⊢
    by_cases h : v ∈ a
    · have h' : f v ∈ a.map f := hiff.mpr h
      simpa [h, h'] using hev
    · have h' : f v ∉ a.map f := fun hc => h (hiff.mp hc)
      simpa [h, h'] using hev
