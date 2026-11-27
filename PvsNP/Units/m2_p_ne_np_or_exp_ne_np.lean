import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_not_in_p

namespace PvsNP.Units.m2_p_ne_np_or_exp_ne_np

end PvsNP.Units.m2_p_ne_np_or_exp_ne_np

/-- P ≠ NP or some exponential-time language is outside NP (TM2): if P = NP, the
language of the settled unit `m2_exp_not_in_p` is exponential-time and outside P,
hence outside NP. -/
theorem PvsNP.Units.m2_p_ne_np_or_exp_ne_np :
    PvsNP.P ≠ PvsNP.NP ∨ ∃ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool)
          (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧
      L ∉ PvsNP.NP := by
  by_cases h : PvsNP.P = PvsNP.NP
  · right
    obtain ⟨L, hexp, hP⟩ := PvsNP.Units.m2_exp_not_in_p
    refine ⟨L, hexp, ?_⟩
    rw [← h]
    exact hP
  · left
    exact h
