import Mathlib
import PvsNP.Defs
import CookLevin

/-- A conjunction of literals is satisfiable exactly when it holds no complementary pair. -/
theorem PvsNP.Units.m3_dnf_term_sat :
    ∀ T : List literal, (∃ a : assgn, T.all (evalLiteral a) = true) ↔
      ∀ l ∈ T, (!l.1, l.2) ∉ T := by
  intro T
  constructor
  · rintro ⟨a, ha⟩ ⟨s, v⟩ hl hneg
    rw [List.all_eq_true] at ha
    have h1 := ha (s, v) hl
    have h2 := ha (!s, v) hneg
    simp only [evalLiteral, decide_eq_true_eq] at h1 h2
    rw [h1] at h2
    cases s <;> simp at h2
  · intro hno
    refine ⟨(T.filter (fun l => l.1)).map Prod.snd, ?_⟩
    simp only [List.all_eq_true]
    rintro ⟨s, v⟩ hl
    cases s
    · have : v ∉ (T.filter (fun l => l.1)).map Prod.snd := by
        intro hv
        obtain ⟨⟨s', v'⟩, hm, rfl⟩ := List.mem_map.mp hv
        obtain ⟨hf, hs⟩ := List.mem_filter.mp hm
        subst hs
        exact hno _ hl hf
      revert this
      generalize (T.filter (fun l => l.1)).map Prod.snd = a
      intro this
      simp [evalLiteral, evalVar, this]
    · have : v ∈ (T.filter (fun l => l.1)).map Prod.snd :=
        List.mem_map.mpr ⟨(true, v), List.mem_filter.mpr ⟨hl, rfl⟩, rfl⟩
      revert this
      generalize (T.filter (fun l => l.1)).map Prod.snd = a
      intro this
      simp [evalLiteral, evalVar, this]
