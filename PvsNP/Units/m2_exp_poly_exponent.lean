import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_exp_poly_exponent

theorem two_pow_add_le (a b : ℕ) : 2 ^ a + b ≤ 2 ^ (a + b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hpos : 1 ≤ 2 ^ (a + b) := Nat.one_le_two_pow
    have hpow : 2 ^ (a + (b + 1)) = 2 ^ (a + b) * 2 := by
      rw [← Nat.add_assoc, Nat.pow_succ]
    rw [hpow]
    omega

theorem eval_le_eval_one_mul_pow (p : Polynomial ℕ) {n : ℕ} (hn : 1 ≤ n) :
    p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun e he => ?_
  have hed : e ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp e he
  have hpow : n ^ e ≤ n ^ p.natDegree := Nat.pow_le_pow_right hn hed
  simp only [one_pow, mul_one]
  exact Nat.mul_le_mul_left (p.coeff e) hpow

theorem exp_poly_bound (p : Polynomial ℕ) :
    ∃ k : ℕ, ∀ n : ℕ, 2 ^ p.eval n ≤ 2 ^ (n ^ k) + k := by
  let k : ℕ := 2 ^ p.eval 0 + 2 ^ p.eval 1 + p.natDegree
  refine ⟨k, fun n => ?_⟩
  match n with
  | 0 =>
    have h0 : 2 ^ p.eval 0 ≤ k :=
      (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    exact h0.trans (Nat.le_add_left k _)
  | 1 =>
    have h1 : 2 ^ p.eval 1 ≤ k :=
      (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    exact h1.trans (Nat.le_add_left k _)
  | m + 2 =>
    have hge1 : 1 ≤ m + 2 := by omega
    have hge2 : 2 ≤ m + 2 := by omega
    have h1 : p.eval (m + 2) ≤ p.eval 1 * (m + 2) ^ p.natDegree :=
      eval_le_eval_one_mul_pow p hge1
    have h2 : p.eval 1 ≤ 2 ^ p.eval 1 := Nat.le_of_lt Nat.lt_two_pow_self
    have h3 : 2 ^ p.eval 1 ≤ (m + 2) ^ p.eval 1 := Nat.pow_le_pow_left hge2 (p.eval 1)
    have h4 : p.eval (m + 2) ≤ (m + 2) ^ (p.eval 1 + p.natDegree) := by
      calc p.eval (m + 2)
          ≤ p.eval 1 * (m + 2) ^ p.natDegree := h1
        _ ≤ (m + 2) ^ p.eval 1 * (m + 2) ^ p.natDegree :=
            Nat.mul_le_mul_right _ (h2.trans h3)
        _ = (m + 2) ^ (p.eval 1 + p.natDegree) := (Nat.pow_add (m + 2) _ _).symm
    have hle_k : p.eval 1 + p.natDegree ≤ k :=
      Nat.add_le_add_right (h2.trans (Nat.le_add_left _ _)) p.natDegree
    have h5 : (m + 2) ^ (p.eval 1 + p.natDegree) ≤ (m + 2) ^ k :=
      Nat.pow_le_pow_right hge1 hle_k
    have h6 : 2 ^ p.eval (m + 2) ≤ 2 ^ ((m + 2) ^ k) :=
      Nat.pow_le_pow_right (by omega) (h4.trans h5)
    exact h6.trans (Nat.le_add_right _ k)

theorem exp_poly_exponent_aux (L : Language Bool) :
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ↔
    ∃ (p : Polynomial ℕ) (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ p.eval n := by
  constructor
  · rintro ⟨k, f, M, hdec, htime⟩
    refine ⟨Polynomial.X ^ k + Polynomial.C k, f, M, hdec, fun n => ?_⟩
    have h1 := htime n
    have h2 : (Polynomial.X ^ k + Polynomial.C k).eval n = n ^ k + k := by
      simp
    rw [h2]
    exact h1.trans (two_pow_add_le (n ^ k) k)
  · rintro ⟨p, f, M, hdec, htime⟩
    obtain ⟨k, hk⟩ := exp_poly_bound p
    exact ⟨k, f, M, hdec, fun n => (htime n).trans (hk n)⟩

end PvsNP.Units.m2_exp_poly_exponent

/-- EXP is unchanged if the time exponent is any polynomial instead of n ^ k. -/
theorem PvsNP.Units.m2_exp_poly_exponent :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ↔
      ∃ (p : Polynomial ℕ) (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ p.eval n :=
  PvsNP.Units.m2_exp_poly_exponent.exp_poly_exponent_aux
