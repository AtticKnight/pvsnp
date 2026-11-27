import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_eb_poly

/-- Adapted from github.com/brilliant-hq/pequalnp-proofs at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its file
`lean/PEqualNP/Library/Helpers/PolyExp.lean` (as joined into the settled unit
`PvsNP.Units.fr_ladner`). Every polynomial over ℕ is bounded by `n ↦ n ^ k + k`. -/
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

end PvsNP.Units.m2_eb_poly

/-- A polynomial of an exponentially bounded function is exponentially bounded too:
bound `p` by `m ↦ m ^ k + k`, evaluate at the bound of `f`, and absorb the additive
constant `k` into the exponential by taking a slightly larger `A` and `D + 1`. -/
theorem PvsNP.Units.m2_eb_poly :
    ∀ (p : Polynomial ℕ) (f : ℕ → ℕ), (∃ A D : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (A * (n + 1) ^ D)) →
      ∃ A D : ℕ, ∀ n : ℕ, p.eval (f n) ≤ 2 ^ (A * (n + 1) ^ D) := by
  intro p f ⟨A, D, hf⟩
  obtain ⟨k, hk⟩ := PvsNP.Units.m2_eb_poly.polynomial_le_pow_add p
  refine ⟨A * k + k + 2, D + 1, fun n => ?_⟩
  have h2 : (f n) ^ k ≤ (2 ^ (A * (n + 1) ^ D)) ^ k := Nat.pow_le_pow_left (hf n) k
  have h3 : (2 ^ (A * (n + 1) ^ D)) ^ k = 2 ^ (A * k * (n + 1) ^ D) := by
    rw [← pow_mul]
    congr 1
    ring
  have hM : max (A * k * (n + 1) ^ D) k + 1 ≤ (A * k + k + 2) * (n + 1) ^ (D + 1) := by
    have h1 : (n + 1) ^ D ≤ (n + 1) ^ (D + 1) :=
      pow_le_pow_right₀ (show (1 : ℕ) ≤ n + 1 by omega) (Nat.le_succ D)
    have hE : A * k * (n + 1) ^ D + 1 ≤ (A * k + k + 2) * (n + 1) ^ (D + 1) := by
      have hpos : 0 < (n + 1) ^ D := by positivity
      calc A * k * (n + 1) ^ D + 1
          ≤ (A * k + 1) * (n + 1) ^ D := by
            have heq : (A * k + 1) * (n + 1) ^ D = A * k * (n + 1) ^ D + (n + 1) ^ D := by ring
            omega
        _ ≤ (A * k + k + 2) * (n + 1) ^ D :=
            mul_le_mul_of_nonneg_right (by omega) (Nat.zero_le _)
        _ ≤ (A * k + k + 2) * (n + 1) ^ (D + 1) :=
            mul_le_mul_of_nonneg_left h1 (Nat.zero_le _)
    have hk1 : k + 1 ≤ (A * k + k + 2) * (n + 1) ^ (D + 1) := by
      have hpos : 0 < (n + 1) ^ (D + 1) := by positivity
      calc k + 1 ≤ A * k + k + 2 := by omega
        _ = (A * k + k + 2) * 1 := by ring
        _ ≤ (A * k + k + 2) * (n + 1) ^ (D + 1) :=
            mul_le_mul_of_nonneg_left (show (1 : ℕ) ≤ (n + 1) ^ (D + 1) from hpos)
              (Nat.zero_le _)
    omega
  have hfin : 2 ^ (A * k * (n + 1) ^ D) + k ≤
      2 ^ ((A * k + k + 2) * (n + 1) ^ (D + 1)) := by
    have h2k : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    have hE2 : 2 ^ (A * k * (n + 1) ^ D) ≤ 2 ^ max (A * k * (n + 1) ^ D) k :=
      pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
    have hk2 : 2 ^ k ≤ 2 ^ max (A * k * (n + 1) ^ D) k :=
      pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
    have hM1 : 2 ^ max (A * k * (n + 1) ^ D) k + 2 ^ max (A * k * (n + 1) ^ D) k
        = 2 ^ (max (A * k * (n + 1) ^ D) k + 1) := by
      rw [pow_succ]; ring
    have hMle : 2 ^ (max (A * k * (n + 1) ^ D) k + 1) ≤
        2 ^ ((A * k + k + 2) * (n + 1) ^ (D + 1)) :=
      pow_le_pow_right₀ (by norm_num) hM
    calc 2 ^ (A * k * (n + 1) ^ D) + k
        ≤ 2 ^ max (A * k * (n + 1) ^ D) k + 2 ^ k := Nat.add_le_add hE2 h2k
      _ ≤ 2 ^ max (A * k * (n + 1) ^ D) k + 2 ^ max (A * k * (n + 1) ^ D) k :=
          Nat.add_le_add_left hk2 _
      _ = 2 ^ (max (A * k * (n + 1) ^ D) k + 1) := hM1
      _ ≤ 2 ^ ((A * k + k + 2) * (n + 1) ^ (D + 1)) := hMle
  calc p.eval (f n) ≤ (f n) ^ k + k := hk (f n)
    _ ≤ (2 ^ (A * (n + 1) ^ D)) ^ k + k := Nat.add_le_add_right h2 k
    _ = 2 ^ (A * k * (n + 1) ^ D) + k := by rw [h3]
    _ ≤ 2 ^ ((A * k + k + 2) * (n + 1) ^ (D + 1)) := hfin
