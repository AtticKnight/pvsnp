import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_karp_trans
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_p_trivial

open PvsNP.Units

/-- A Ladner intermediate language has a member and a nonmember. A reduction
from any complete language would transfer hardness by composition. -/
theorem PvsNP.Units.m2_p_ne_np_ladner_props :
    PvsNP.P ≠ PvsNP.NP → ∃ L ∈ PvsNP.NP, L ∉ PvsNP.P ∧
      (∃ y : List Bool, y ∈ L) ∧ (∃ z : List Bool, z ∉ L) ∧
      ∀ L₀ : Language Bool, PvsNP.NPComplete L₀ → ¬ PvsNP.KarpReducible L₀ L := by
  classical
  intro hne
  have separation : ∃ A ∈ PvsNP.NP, A ∉ PvsNP.P := by
    by_contra hn
    apply hne
    apply Set.Subset.antisymm m2_p_subset_np
    intro A hA
    by_contra hA'
    exact hn ⟨A, hA, hA'⟩
  obtain ⟨L, hNP, hP, hIncomplete⟩ := fr_ladner separation
  refine ⟨L, hNP, hP, ?_, ?_, ?_⟩
  · by_contra hn
    apply hP
    have he : L = ∅ := by
      ext x
      exact ⟨fun hx => (hn ⟨x, hx⟩).elim, fun hx => False.elim hx⟩
    rw [he]
    exact m2_p_trivial.1
  · by_contra hn
    apply hP
    have hu : L = Set.univ := by
      ext x
      refine ⟨fun _ => Set.mem_univ x, fun _ => ?_⟩
      by_contra hx
      exact hn ⟨x, hx⟩
    rw [hu]
    exact m2_p_trivial.2
  · intro L₀ hComplete reduction
    apply hIncomplete
    refine ⟨hNP, ?_⟩
    intro A hA
    exact m2_karp_trans A L₀ L (hComplete.2 A hA) reduction
