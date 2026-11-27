import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_poly_normal

/-
Adapted from github.com/brilliant-hq/pequalnp-proofs at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its file
  lean/PEqualNP/Library/L044.lean.
MODIFIED from that file: the polynomial bound comes from the settled unit
PvsNP.Units.m2_p_poly_normal (its `polynomial_le_pow_add`), the machine is forgotten to a
plain `Turing.TM2ComputableInTime` with `Polynomial.eval` as its time function, and the
closing theorem is stated for `PvsNP.P` with the bound `2 ^ (n ^ k) + k`.
-/

theorem PvsNP.Units.m2_p_subset_exp :
    ∀ L ∈ PvsNP.P, ∃ k : ℕ,
      ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L hL
  obtain ⟨f, ⟨M⟩, hf⟩ := hL
  obtain ⟨k, hk⟩ := PvsNP.Units.m2_p_poly_normal.polynomial_le_pow_add M.time
  refine ⟨k, f, M.toTM2ComputableInTime, hf, fun n => ?_⟩
  exact (hk n).trans (Nat.add_le_add_right (Nat.lt_two_pow_self).le k)
