import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_poly_normal
import PvsNP.Units.m2_exp_no_fixed_exponent

set_option autoImplicit false

namespace PvsNP.Units.m2_exp_no_fixed_poly_exponent

private theorem bound (K n : ℕ) :
    2 ^ (n ^ K + K) ≤ 2 ^ (n ^ (2 ^ (K + 1) + K + 1)) + (2 ^ (K + 1) + K + 1) := by
  set j := 2 ^ (K + 1) + K + 1
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hn1 : n ^ K ≤ 1 := by
      have := Nat.pow_le_pow_left (show n ≤ 1 by omega) K
      simpa using this
    have hpow : 2 ^ (n ^ K + K) ≤ 2 ^ (K + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hj : 2 ^ (K + 1) ≤ j := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    exact le_trans hpow (le_trans hj (Nat.le_add_left _ _))
  · have hK1 : K ≤ 2 ^ K := Nat.le_of_lt Nat.lt_two_pow_self
    have hK2 : 2 ^ K ≤ n ^ K := Nat.pow_le_pow_left (by omega) K
    have hmul : 2 * n ^ K ≤ n * n ^ K := Nat.mul_le_mul_right _ (by omega)
    have hpow1 : n * n ^ K = n ^ (K + 1) := by rw [pow_succ']
    have hpow2 : n ^ (K + 1) ≤ n ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    have hexp : n ^ K + K ≤ n ^ j := by omega
    have h2 : 2 ^ (n ^ K + K) ≤ 2 ^ (n ^ j) := Nat.pow_le_pow_right (by decide) hexp
    omega

theorem main (p : Polynomial ℕ) :
    ∃ L : Language Bool, (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧
      ¬ ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ p.eval n := by
  obtain ⟨K, hK⟩ := PvsNP.Units.m2_p_poly_normal.polynomial_le_pow_add p
  set j := 2 ^ (K + 1) + K + 1
  obtain ⟨L, hExp, hNo⟩ := PvsNP.Units.m2_exp_no_fixed_exponent j
  refine ⟨L, hExp, ?_⟩
  rintro ⟨f, M, hf, hM⟩
  exact hNo ⟨f, M, hf, fun n =>
    le_trans (hM n) (le_trans (Nat.pow_le_pow_right (by decide) (hK n)) (bound K n))⟩

end PvsNP.Units.m2_exp_no_fixed_poly_exponent

theorem PvsNP.Units.m2_exp_no_fixed_poly_exponent :
    ∀ p : Polynomial ℕ, ∃ L : Language Bool, (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧
      ¬ ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ p.eval n :=
  PvsNP.Units.m2_exp_no_fixed_poly_exponent.main
