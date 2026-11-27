import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_not_in_p
import PvsNP.Units.m2_p_down_closed

theorem PvsNP.Units.m2_exp_hard_not_in_p :
    ∀ L : Language Bool,
      (∀ L' : Language Bool,
        (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
              (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
          PvsNP.KarpReducible L' L) →
      L ∉ PvsNP.P := by
  intro L hL hLP
  obtain ⟨L₀, hexp, hnotP⟩ := PvsNP.Units.m2_exp_not_in_p
  have hred := hL L₀ hexp
  exact hnotP (PvsNP.Units.m2_p_down_closed L₀ L hred hLP)
