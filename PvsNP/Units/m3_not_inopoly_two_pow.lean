import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_not_inopoly_two_pow : ¬ inOPoly (fun n => 2 ^ n) := by
  rintro ⟨k, c, n0, h⟩
  have hm : ∀ m : ℕ, m < 2 ^ m := fun m => Nat.lt_two_pow_self
  let m := c * (k + 1) ^ k + n0
  have h1 := h ((k + 1) * m) (by
    have : m ≤ (k + 1) * m := Nat.le_mul_of_pos_left m (Nat.succ_pos k)
    omega)
  simp only at h1
  have hD : c * (k + 1) ^ k < 2 ^ m := lt_of_le_of_lt (Nat.le_add_right _ _) (hm m)
  have hk : m ^ k ≤ (2 ^ m) ^ k := Nat.pow_le_pow_left (Nat.le_of_lt (hm m)) k
  have h2 : c * (k + 1) ^ k * m ^ k < 2 ^ m * (2 ^ m) ^ k :=
    Nat.mul_lt_mul_of_lt_of_le hD hk (Nat.pos_of_ne_zero (by positivity))
  have e1 : c * ((k + 1) * m) ^ k = c * (k + 1) ^ k * m ^ k := by rw [mul_pow, mul_assoc]
  have e2 : (2 : ℕ) ^ ((k + 1) * m) = 2 ^ m * (2 ^ m) ^ k := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [e1, e2] at h1
  omega
