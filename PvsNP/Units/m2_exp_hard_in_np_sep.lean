import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_not_in_p
import PvsNP.Units.m2_p_down_closed

theorem PvsNP.Units.m2_exp_hard_in_np_sep : ∀ L : Language Bool,
  (∀ L' : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      PvsNP.KarpReducible L' L) →
  L ∈ PvsNP.NP → PvsNP.P ≠ PvsNP.NP := by
  intro L hHard hNP hEq
  obtain ⟨L', hEXP, hnotP⟩ := PvsNP.Units.m2_exp_not_in_p
  exact hnotP (PvsNP.Units.m2_p_down_closed L' L (hHard L' hEXP) (hEq ▸ hNP))
