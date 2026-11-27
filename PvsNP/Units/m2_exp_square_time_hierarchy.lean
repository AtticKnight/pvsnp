import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_time_hierarchy_gen
import PvsNP.Units.m2_exp_clock

set_option autoImplicit false

/-- Exponential time hierarchy at exponent n²: instantiate the general hierarchy with
t n = 2^(n²); the settled exponential clock at k = 2 supplies the required clock machine. -/
theorem PvsNP.Units.m2_exp_square_time_hierarchy :
    ∃ k : ℕ, ∃ L : Language Bool,
      (∃ c : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ c * 2 ^ (k * n ^ 2) + c) ∧
      ¬ ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ 2) := by
  obtain ⟨k, hk⟩ := PvsNP.Units.m2_time_hierarchy_gen
  have hclock : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (2 ^ (x.length ^ 2)) true)),
      ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ 2) + c :=
    PvsNP.Units.m2_exp_clock 2 (by norm_num)
  obtain ⟨L, ⟨c, f, M, hf, hM⟩, hno⟩ :=
    hk (fun n : ℕ => 2 ^ (n ^ 2)) (fun n => by
    by_cases hz : n = 0
    · simp [hz]
    have hn : n ≤ n ^ 2 := Nat.le_pow zero_lt_two
    exact (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_right (by norm_num) hn)) hclock
  refine ⟨k, L, ⟨c, f, M, hf, fun n => ?_⟩, hno⟩
  have h := hM n
  have hpow : (2 ^ (n ^ 2)) ^ k = 2 ^ (k * n ^ 2) := by
    rw [← pow_mul]
    congr 1
    exact Nat.mul_comm _ _
  rw [hpow] at h
  exact h
