import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_p_subset_np

/-
Closes m2_p_ne_np_iff_intermediate: `P ≠ NP` implies some language in `NP \ P`
(since `P ⊆ NP` by `m2_p_subset_np`), which yields an NP-intermediate language
by Ladner's theorem (`fr_ladner`); conversely, any language in `NP \ P`
separates `P` and `NP`.
-/

set_option autoImplicit false

/-- `P ≠ NP` exactly when some NP language is neither in P nor NP-complete (TM2). -/
theorem PvsNP.Units.m2_p_ne_np_iff_intermediate :
    PvsNP.P ≠ PvsNP.NP ↔ ∃ L ∈ PvsNP.NP, L ∉ PvsNP.P ∧ ¬ PvsNP.NPComplete L := by
  constructor
  · intro hne
    have hex : ∃ L ∈ PvsNP.NP, L ∉ PvsNP.P := by
      by_contra hall
      apply hne
      apply Set.Subset.antisymm PvsNP.Units.m2_p_subset_np
      intro L hL
      by_contra hnP
      exact hall ⟨L, hL, hnP⟩
    exact PvsNP.Units.fr_ladner hex
  · rintro ⟨L, hNP, hnP, _⟩ heq
    rw [← heq] at hNP
    exact hnP hNP
