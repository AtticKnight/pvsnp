import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_eb_final

theorem le_two_pow_self (a : ℕ) : a ≤ 2 ^ a := by
  induction a with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hp : 0 < 2 ^ k := pow_pos (by norm_num) k
    rw [pow_succ]
    omega

theorem exp_le (A D n j : ℕ) (hn : 2 ≤ n) (hj : A + 2 * D ≤ j) :
    A * (n + 1) ^ D ≤ n ^ j := by
  have hA : A ≤ n ^ A := le_trans (le_two_pow_self A) (Nat.pow_le_pow_left hn A)
  have hsq : n + 1 ≤ n ^ 2 := by nlinarith
  have hD : (n + 1) ^ D ≤ n ^ (2 * D) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hsq D
  calc A * (n + 1) ^ D ≤ n ^ A * n ^ (2 * D) := Nat.mul_le_mul hA hD
    _ = n ^ (A + 2 * D) := (pow_add n A (2 * D)).symm
    _ ≤ n ^ j := Nat.pow_le_pow_right (by omega) hj

end PvsNP.Units.m2_eb_final

theorem PvsNP.Units.m2_eb_final : ∀ f : ℕ → ℕ, (∃ A D : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (A * (n + 1) ^ D)) → ∃ j : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (n ^ j) + j := by
  rintro f ⟨A, D, h⟩
  refine ⟨A + 2 * D + f 0 + f 1, fun n => ?_⟩
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h01 : f n ≤ A + 2 * D + f 0 + f 1 := by
      rcases Nat.lt_or_ge n 1 with h0 | h1
      · have hn0 : n = 0 := by omega
        subst hn0
        omega
      · have hn1 : n = 1 := by omega
        subst hn1
        omega
    exact le_trans h01 (Nat.le_add_left _ _)
  · calc f n ≤ 2 ^ (A * (n + 1) ^ D) := h n
      _ ≤ 2 ^ (n ^ (A + 2 * D + f 0 + f 1)) :=
        Nat.pow_le_pow_right (by norm_num)
          (PvsNP.Units.m2_eb_final.exp_le A D n _ hn (by omega))
      _ ≤ 2 ^ (n ^ (A + 2 * D + f 0 + f 1)) + (A + 2 * D + f 0 + f 1) :=
        Nat.le_add_right _ _
