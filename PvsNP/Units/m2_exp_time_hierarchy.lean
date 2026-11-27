import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_time_hierarchy_gen
import PvsNP.Units.m2_exp_clock

/-!
Exponential time hierarchy on Mathlib's TM2: the settled general hierarchy
`PvsNP.Units.m2_time_hierarchy_gen` at `t n = 2 ^ n`, with the clock `x ↦ 1^(2^|x|)` supplied by
the settled `PvsNP.Units.m2_exp_clock` at `k = 1`; then `(2 ^ n) ^ k = 2 ^ (k * n)`.
-/

theorem PvsNP.Units.m2_exp_time_hierarchy : ∃ L : Language Bool,
  (∃ (c k : ℕ) (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ c * 2 ^ (k * n) + c) ∧
  ¬ ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ n := by
  obtain ⟨k, hk⟩ := PvsNP.Units.m2_time_hierarchy_gen
  have hclock : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (2 ^ x.length) true)),
      ∀ n : ℕ, M.time n ≤ c * 2 ^ n + c := by
    have h := PvsNP.Units.m2_exp_clock 1 le_rfl
    have heq : (fun x : List Bool => List.replicate (2 ^ (x.length ^ 1)) true) =
        (fun x : List Bool => List.replicate (2 ^ x.length) true) := by
      funext x
      rw [pow_one]
    rw [heq] at h
    simpa only [pow_one] using h
  obtain ⟨L, ⟨c, f, M, hf, hM⟩, hno⟩ :=
    hk (fun n : ℕ => 2 ^ n) (fun n => Nat.le_of_lt Nat.lt_two_pow_self) hclock
  refine ⟨L, ⟨c, k, f, M, hf, fun n => ?_⟩, hno⟩
  have h := hM n
  rw [pow_mul']
  exact h
