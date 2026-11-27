import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_bounded_slice
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_p_compl

theorem PvsNP.Units.m2_z_bounded_length_classes : ∀ (L : Language Bool) (m : ℕ), (∀ x ∈ L, x.length ≤ m) →
  L ∈ PvsNP.P ∧ L ∈ PvsNP.NP ∧ L ∈ PvsNP.coNP := by
  intro L m h
  have hs := PvsNP.Units.m2_p_bounded_slice L m
  have e : ({x : List Bool | x ∈ L ∧ x.length ≤ m} : Language Bool) = L := by
    ext x
    constructor
    · rintro ⟨hx, _⟩
      exact hx
    · intro hx
      exact ⟨hx, h x hx⟩
  rw [e] at hs
  refine ⟨hs, PvsNP.Units.m2_p_subset_np hs, ?_⟩
  show Lᶜ ∈ PvsNP.NP
  exact PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_p_compl L hs)
