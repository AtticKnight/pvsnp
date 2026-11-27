import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_conp_one_inclusion
import PvsNP.Units.m2_np_conp_subset_exp

/-- Restrict the assumed EXP-to-NP inclusion to coNP, then use closure under taking complements. -/
theorem PvsNP.Units.m2_np_eq_exp_np_conp :
    (∀ L : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      L ∈ PvsNP.NP) →
  PvsNP.NP = PvsNP.coNP := by
  intro incl
  apply PvsNP.Units.m2_np_conp_one_inclusion.2.1
  intro L hL
  exact incl L (PvsNP.Units.m2_np_conp_subset_exp L (Or.inr hL))
