import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m2_eb_two_pow :
    ∀ (f : ℕ → ℕ) (A D K : ℕ), (∀ n : ℕ, f n ≤ A * (n + 1) ^ D) →
      ∃ B E : ℕ, ∀ n : ℕ, 2 ^ (f n ^ K) ≤ 2 ^ (B * (n + 1) ^ E) := by
  intro f A D K hf
  refine ⟨A ^ K, D * K, fun n => ?_⟩
  refine Nat.pow_le_pow_right (by decide) ?_
  calc
    f n ^ K ≤ (A * (n + 1) ^ D) ^ K := Nat.pow_le_pow_left (hf n) K
    _ = A ^ K * ((n + 1) ^ D) ^ K := Nat.mul_pow _ _ _
    _ = A ^ K * (n + 1) ^ (D * K) := by rw [← pow_mul]
