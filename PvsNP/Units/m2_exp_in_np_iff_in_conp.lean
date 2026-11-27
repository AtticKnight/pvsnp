import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_compl

/-- All of exponential time is in NP exactly when all of it is in coNP (TM2). -/
theorem PvsNP.Units.m2_exp_in_np_iff_in_conp :
    (∀ L : Language Bool, (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
              (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) → L ∈ PvsNP.NP) ↔
      ∀ L : Language Bool, (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) → L ∈ PvsNP.coNP := by
  constructor
  · intro h L hL
    exact h Lᶜ (PvsNP.Units.m2_exp_compl L hL)
  · intro h L hL
    have hc : Lᶜ ∈ PvsNP.coNP := h Lᶜ (PvsNP.Units.m2_exp_compl L hL)
    change Lᶜᶜ ∈ PvsNP.NP at hc
    rwa [compl_compl] at hc
