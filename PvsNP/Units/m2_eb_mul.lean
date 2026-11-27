import Mathlib
import PvsNP.Defs
import CookLevin

/-- Functions below 2^(A·(n+1)^D) are closed under products. -/
theorem PvsNP.Units.m2_eb_mul :
    ∀ f g : ℕ → ℕ,
      (∃ A D : ℕ, ∀ n : ℕ, f n ≤ 2 ^ (A * (n + 1) ^ D)) →
      (∃ A D : ℕ, ∀ n : ℕ, g n ≤ 2 ^ (A * (n + 1) ^ D)) →
      ∃ A D : ℕ, ∀ n : ℕ, f n * g n ≤ 2 ^ (A * (n + 1) ^ D) := by
  rintro f g ⟨A, D, hf⟩ ⟨B, E, hg⟩
  refine ⟨A + B, D + E, fun n => ?_⟩
  have hD : (n + 1) ^ D ≤ (n + 1) ^ (D + E) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hE : (n + 1) ^ E ≤ (n + 1) ^ (D + E) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hsum : A * (n + 1) ^ D + B * (n + 1) ^ E ≤ (A + B) * (n + 1) ^ (D + E) := by
    calc A * (n + 1) ^ D + B * (n + 1) ^ E
        ≤ A * (n + 1) ^ (D + E) + B * (n + 1) ^ (D + E) :=
          Nat.add_le_add (Nat.mul_le_mul (le_refl A) hD) (Nat.mul_le_mul (le_refl B) hE)
      _ = (A + B) * (n + 1) ^ (D + E) := by ring
  calc f n * g n
      ≤ 2 ^ (A * (n + 1) ^ D) * 2 ^ (B * (n + 1) ^ E) := Nat.mul_le_mul (hf n) (hg n)
    _ = 2 ^ (A * (n + 1) ^ D + B * (n + 1) ^ E) := by rw [← pow_add]
    _ ≤ 2 ^ ((A + B) * (n + 1) ^ (D + E)) :=
        Nat.pow_le_pow_right (by norm_num) hsum
