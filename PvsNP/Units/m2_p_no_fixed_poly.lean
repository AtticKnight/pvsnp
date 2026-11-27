import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.m2_p_poly_normal

import PvsNP.Units.m2_p_time_hierarchy

/-- No single polynomial bounds the running time of every language in `P`: given any
polynomial `p`, `polynomial_le_pow_add` gives `k` with `p.eval n ≤ n ^ k + k`, and the
time-hierarchy language at that `k` lies in `P` but is not decidable within `n ^ k + k`
steps, contradicting the bound `p` would impose on it. -/
theorem PvsNP.Units.m2_p_no_fixed_poly :
    ¬ ∃ p : Polynomial ℕ, ∀ L ∈ PvsNP.P,
      ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ p.eval n := by
  rintro ⟨p, hp⟩
  obtain ⟨k, hk⟩ := PvsNP.Units.m2_p_poly_normal.polynomial_le_pow_add p
  obtain ⟨L, hLP, hL⟩ := PvsNP.Units.m2_p_time_hierarchy k
  obtain ⟨f, M, hf, htime⟩ := hp L hLP
  exact hL ⟨f, M, hf, fun n => (htime n).trans (hk n)⟩
