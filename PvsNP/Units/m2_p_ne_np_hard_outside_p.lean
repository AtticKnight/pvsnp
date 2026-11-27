import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.m2_nphard_in_p_iff

import PvsNP.Units.m2_p_down_closed

import PvsNP.Units.m2_p_compl

import PvsNP.Units.m2_p_subset_np

set_option autoImplicit false

/-- If `P ≠ NP`, no NP-hard and no coNP-hard language is in P: NP-hard follows
from the settled unit `m2_nphard_in_p_iff`; coNP-hard puts all of coNP in P
by downward closure (`m2_p_down_closed`), hence all of NP in P by complements
(`m2_p_compl`), and `P ⊆ NP` then forces `P = NP`. -/
theorem PvsNP.Units.m2_p_ne_np_hard_outside_p :
    PvsNP.P ≠ PvsNP.NP → ∀ L : Language Bool,
      (PvsNP.NPHard L → L ∉ PvsNP.P) ∧ ((∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' L) → L ∉ PvsNP.P) := by
  intro hne L
  refine ⟨?_, ?_⟩
  · intro hhard hLP
    exact hne (PvsNP.Units.m2_nphard_in_p_iff.mp ⟨L, hhard, hLP⟩)
  · intro hco hLP
    have hcoNP : ∀ M : Language Bool, M ∈ PvsNP.coNP → M ∈ PvsNP.P :=
      fun M hM => PvsNP.Units.m2_p_down_closed M L (hco M hM) hLP
    have hNPsubP : PvsNP.NP ⊆ PvsNP.P := by
      intro M hM
      have h1 := hcoNP Mᶜ (by show (Mᶜ)ᶜ ∈ PvsNP.NP; rw [compl_compl]; exact hM)
      have h2 := PvsNP.Units.m2_p_compl Mᶜ h1
      rwa [compl_compl] at h2
    exact hne (Set.Subset.antisymm PvsNP.Units.m2_p_subset_np hNPsubP)
