import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_eb_add

lemma pow_le_pow_of_le_D (n D D' : ℕ) (h : D ≤ D') : (n + 1) ^ D ≤ (n + 1) ^ D' :=
  Nat.pow_le_pow_right (Nat.succ_pos n) h

end PvsNP.Units.m2_eb_add

theorem PvsNP.Units.m2_eb_add :
    ∀ f g : ℕ → ℕ, (∃ A D : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (A * (n + 1) ^ D)) →
      (∃ A D : ℕ, ∀ n : ℕ, g n ≤ 2 ^ (A * (n + 1) ^ D)) →
        ∃ A D : ℕ, ∀ n : ℕ, f n + g n ≤ 2 ^ (A * (n + 1) ^ D) := by
  rintro f g ⟨A1, D1, h1⟩ ⟨A2, D2, h2⟩
  refine ⟨A1 + A2 + 1, D1 + D2, fun n => ?_⟩
  set P := (n + 1) ^ (D1 + D2) with hP
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have e1 : A1 * (n + 1) ^ D1 ≤ (A1 + A2) * P := by
    have := PvsNP.Units.m2_eb_add.pow_le_pow_of_le_D n D1 (D1 + D2) (Nat.le_add_right _ _)
    calc A1 * (n + 1) ^ D1 ≤ A1 * P := Nat.mul_le_mul_left _ this
      _ ≤ (A1 + A2) * P := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have e2 : A2 * (n + 1) ^ D2 ≤ (A1 + A2) * P := by
    have := PvsNP.Units.m2_eb_add.pow_le_pow_of_le_D n D2 (D1 + D2) (Nat.le_add_left _ _)
    calc A2 * (n + 1) ^ D2 ≤ A2 * P := Nat.mul_le_mul_left _ this
      _ ≤ (A1 + A2) * P := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  have b1 : f n ≤ 2 ^ ((A1 + A2) * P) :=
    (h1 n).trans (Nat.pow_le_pow_right (by norm_num) e1)
  have b2 : g n ≤ 2 ^ ((A1 + A2) * P) :=
    (h2 n).trans (Nat.pow_le_pow_right (by norm_num) e2)
  have hexp : (A1 + A2) * P + 1 ≤ (A1 + A2 + 1) * P := by
    have e : (A1 + A2 + 1) * P = (A1 + A2) * P + P := by ring
    omega
  calc f n + g n ≤ 2 ^ ((A1 + A2) * P) + 2 ^ ((A1 + A2) * P) := Nat.add_le_add b1 b2
    _ = 2 ^ ((A1 + A2) * P + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ ((A1 + A2 + 1) * P) := Nat.pow_le_pow_right (by norm_num) hexp
