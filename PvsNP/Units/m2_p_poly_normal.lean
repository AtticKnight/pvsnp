import Mathlib
import PvsNP.Defs
import CookLevin

/-
Adapted from github.com/brilliant-hq/pequalnp-proofs at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its file
  lean/PEqualNP/Library/L004.lean.
MODIFIED from that file: the helper `polynomial_le_pow_add` is copied here, inside the
namespace PvsNP.Units.m2_p_poly_normal in place of PEqualNP.Library.Helpers; the closing
theorem is stated for PvsNP.P and Turing.TM2ComputableInPolyTime. The proof of the helper
is upstream as written.
-/

namespace PvsNP.Units.m2_p_poly_normal

theorem polynomial_le_pow_add (p : Polynomial ℕ) :
    ∃ k : ℕ, ∀ n : ℕ, Polynomial.eval n p ≤ n ^ k + k := by
  have small : ∀ (n e : ℕ), n < 2 → n ^ e ≤ 1 := fun n e hn => by
    have := Nat.pow_le_pow_left (show n ≤ 1 by omega) e
    rwa [Nat.one_pow] at this
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b + 2, fun n => ?_⟩
    rw [Polynomial.eval_add]
    have h1 := ha n
    have h2 := hb n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have e1 := small n a hn
      have e2 := small n b hn
      omega
    · have pa : n ^ a ≤ n ^ (a + b) := Nat.pow_le_pow_right (by omega) (by omega)
      have pb : n ^ b ≤ n ^ (a + b) := Nat.pow_le_pow_right (by omega) (by omega)
      have ps : n ^ (a + b + 1) = n ^ (a + b) * n := Nat.pow_succ ..
      have pt : n ^ (a + b + 1) ≤ n ^ (a + b + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 * n ^ (a + b) ≤ n ^ (a + b) * n := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hn
      omega
  | monomial d c =>
    refine ⟨d + c, fun n => ?_⟩
    rw [Polynomial.eval_monomial]
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have e1 := small n d hn
      calc c * n ^ d ≤ c * 1 := Nat.mul_le_mul_left _ e1
        _ ≤ n ^ (d + c) + (d + c) := by omega
    · have hc : c ≤ n ^ c := (Nat.lt_pow_self (by omega)).le
      calc c * n ^ d ≤ n ^ c * n ^ d := Nat.mul_le_mul_right _ hc
        _ = n ^ (d + c) := by rw [Nat.add_comm, Nat.pow_add]
        _ ≤ n ^ (d + c) + (d + c) := Nat.le_add_right _ _

end PvsNP.Units.m2_p_poly_normal

theorem PvsNP.Units.m2_p_poly_normal :
    ∀ L : Language Bool, L ∈ PvsNP.P ↔
      ∃ (k : ℕ) (f : List Bool → Bool)
        (M : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time.eval n ≤ n ^ k + k := by
  intro L
  constructor
  · intro h
    obtain ⟨f, ⟨M⟩, hf⟩ := h
    obtain ⟨k, hk⟩ := PvsNP.Units.m2_p_poly_normal.polynomial_le_pow_add M.time
    exact ⟨k, f, M, hf, hk⟩
  · rintro ⟨k, f, M, hf, -⟩
    exact ⟨f, ⟨M⟩, hf⟩
