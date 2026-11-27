import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_output_length_poly

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_unary_value_neg

private lemma ofDigits_replicate_true_add_one (n : ℕ) :
    Nat.ofDigits (2 : ℕ) ((List.replicate n true).map Bool.toNat) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.map_cons, Bool.toNat_true, Nat.ofDigits_cons]
    rw [Nat.pow_succ]
    omega

private lemma eval_le_eval_one_mul_pow (q : Polynomial ℕ) {n : ℕ} (hn : 1 ≤ n) :
    q.eval n ≤ q.eval 1 * n ^ q.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hid : i ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [one_pow, mul_one]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn hid)

private lemma exists_poly_lt_two_pow (C k : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧ C * n ^ k + 1 < 2 ^ n := by
  let m : ℕ := C * (k + 1) ^ k + 2
  let n : ℕ := m * (k + 1)
  have hm_pos : 1 ≤ m := by omega
  have hn_pos : 1 ≤ n := Nat.mul_le_mul hm_pos (Nat.succ_le_succ (Nat.zero_le k))
  have hlt : C * (k + 1) ^ k + 1 < 2 ^ m :=
    lt_trans (by omega : C * (k + 1) ^ k + 1 < m) (Nat.lt_two_pow_self)
  have hm_le : m ≤ 2 ^ m := le_of_lt Nat.lt_two_pow_self
  have hmk_pos : 1 ≤ m ^ k := Nat.one_le_pow k m hm_pos
  have hpow_le : m ^ k ≤ (2 ^ m) ^ k := Nat.pow_le_pow_left hm_le k
  have h2mk_pos : 0 < (2 ^ m) ^ k := Nat.pos_of_ne_zero (by positivity)
  refine ⟨n, hn_pos, ?_⟩
  have hstep1 : C * n ^ k + 1 ≤ (C * (k + 1) ^ k + 1) * m ^ k := by
    have hmul : C * n ^ k = C * (k + 1) ^ k * m ^ k := by
      dsimp only [n]
      rw [mul_pow]
      ring
    rw [hmul]
    calc C * (k + 1) ^ k * m ^ k + 1
        ≤ C * (k + 1) ^ k * m ^ k + 1 * m ^ k := by omega
      _ = (C * (k + 1) ^ k + 1) * m ^ k := by ring
  have hstep2 : (C * (k + 1) ^ k + 1) * m ^ k ≤ (C * (k + 1) ^ k + 1) * (2 ^ m) ^ k :=
    Nat.mul_le_mul_left _ hpow_le
  have hstep3 : (C * (k + 1) ^ k + 1) * (2 ^ m) ^ k < 2 ^ m * (2 ^ m) ^ k :=
    Nat.mul_lt_mul_of_pos_right hlt h2mk_pos
  have hstep4 : 2 ^ m * (2 ^ m) ^ k = 2 ^ n := by
    calc 2 ^ m * (2 ^ m) ^ k
        = (2 ^ m) ^ k * 2 ^ m := Nat.mul_comm _ _
      _ = (2 ^ m) ^ (k + 1) := (Nat.pow_succ (2 ^ m) k).symm
      _ = 2 ^ (m * (k + 1)) := (Nat.pow_mul 2 m (k + 1)).symm
      _ = 2 ^ n := rfl
  exact lt_of_le_of_lt hstep1 (lt_of_le_of_lt hstep2 (hstep4 ▸ hstep3))

end PvsNP.Units.tf_fun_unary_value_neg

theorem PvsNP.Units.tf_fun_unary_value_neg :
    ¬ (PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => List.replicate (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)) true)) := by
  intro hf
  obtain ⟨q, hq⟩ := PvsNP.Units.m2_output_length_poly _ hf
  obtain ⟨n, hn, hlt⟩ :=
    PvsNP.Units.tf_fun_unary_value_neg.exists_poly_lt_two_pow (q.eval 1) q.natDegree
  have hbound := hq (List.replicate n true)
  simp only [List.length_replicate] at hbound
  have hqle := PvsNP.Units.tf_fun_unary_value_neg.eval_le_eval_one_mul_pow q hn
  have hdig := PvsNP.Units.tf_fun_unary_value_neg.ofDigits_replicate_true_add_one n
  omega
