import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_eq_np_pi2
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_p_subset_np

/-- P = NP exactly when every Π₂ language over NP is in P: left to right is
the settled collapse `m2_p_eq_np_pi2`; right to left takes the zero
polynomial and the first projection, where the Π₂ language is the NP
language itself, giving NP ⊆ P alongside P ⊆ NP. -/
theorem PvsNP.Units.m2_p_eq_np_iff_pi2_p :
    PvsNP.P = PvsNP.NP ↔ ∀ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.NP → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g →
        ({x : List Bool | ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E} : Language Bool) ∈ PvsNP.P := by
  constructor
  · exact PvsNP.Units.m2_p_eq_np_pi2
  · intro H
    apply Set.Subset.antisymm PvsNP.Units.m2_p_subset_np
    intro E hE
    have h := H E (fun p : List Bool × List Bool => p.1) 0 hE
      PvsNP.Units.m2_pair_split_polytime.1
    have heq : ({x : List Bool | ∀ c : List Bool, c.length ≤ (0 : Polynomial ℕ).eval x.length →
        (fun p : List Bool × List Bool => p.1) (x, c) ∈ E} : Language Bool) = E := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx
        exact hx [] (by simp)
      · intro hx c _
        exact hx
    rwa [heq] at h
