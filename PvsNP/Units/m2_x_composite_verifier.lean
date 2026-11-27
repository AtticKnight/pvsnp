import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_binary_lt
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.tf_fun_pair_mod
import PvsNP.Units.tl_lang_composite_np

namespace PvsNP.Units

namespace m2_x_composite_verifier

open tl_lang_composite_np (val val_bits cpt_bool_eq_const)

private theorem bits_empty_iff (n : ℕ) : Nat.bits n = [] ↔ n = 0 := by
  constructor
  · intro h
    calc n = val (Nat.bits n) := (val_bits n).symm
         _ = val [] := congrArg val h
         _ = 0 := rfl
  · rintro rfl
    rfl

/-- Test both strict bounds on the proposed divisor and use a binary remainder
machine to decide divisibility. Each test reads the same input-certificate pair. -/
theorem verifier_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (1 < val p.2 ∧ val p.2 < val p.1 ∧ val p.2 ∣ val p.1)) := by
  have oneWord : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun _ : List Bool × List Bool => [true]) :=
    m2_polytime_comp _ _ _ _ _ m2_pair_split_polytime.1 (m2_const_polytime [true])
  have oneAndWitness := m2_tm_pair_fork_polytime _ _ oneWord m2_pair_split_polytime.2.1
  have lower : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (1 < val p.2)) :=
    m2_polytime_comp _ _ _ _ _ oneAndWitness m2_tm_binary_lt
  have upper : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (val p.2 < val p.1)) :=
    m2_polytime_comp _ _ _ _ _ m2_tm_pair_swap_polytime m2_tm_binary_lt
  have remZero : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (Nat.bits (val p.1 % val p.2) = [])) :=
    m2_polytime_comp _ _ _ _ _ tf_fun_pair_mod (cpt_bool_eq_const [])
  have hiAndRem := m2_tm_pair_bool_combine Bool.and _ _ upper remZero
  have allThree := m2_tm_pair_bool_combine Bool.and _ _ lower hiAndRem
  have agree :
      (fun p : List Bool × List Bool =>
        decide (1 < val p.2) && (decide (val p.2 < val p.1) && decide (Nat.bits (val p.1 % val p.2) = []))) =
      (fun p : List Bool × List Bool => decide (1 < val p.2 ∧ val p.2 < val p.1 ∧ val p.2 ∣ val p.1)) := by
    funext p
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, bits_empty_iff, Nat.dvd_iff_mod_eq_zero]
  rwa [agree] at allThree

end m2_x_composite_verifier

open tl_lang_composite_np (val val_bits val_lt_two_pow bits_length_le_of_lt_two_pow)

/-- A proper divisor itself is a certificate no longer than the claimed composite. -/
theorem m2_x_composite_verifier :
    PvsNP.PolyTimeVerifier
      ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool)
      (fun p : List Bool × List Bool => decide
        (1 < Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) ∧
         Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ∧
         Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) ∣ Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat)))
      Polynomial.X := by
  refine ⟨m2_x_composite_verifier.verifier_poly, fun x => ?_⟩
  change (∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = val x) ↔
    ∃ w : List Bool, w.length ≤ Polynomial.X.eval x.length ∧
      decide (1 < val w ∧ val w < val x ∧ val w ∣ val x) = true
  simp only [Polynomial.eval_X, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have proper : a < val x := by
      rw [← hab]
      calc a < a + a := by omega
           _ = a * 2 := by omega
           _ ≤ a * b := Nat.mul_le_mul_left a (by omega)
    refine ⟨Nat.bits a, bits_length_le_of_lt_two_pow (proper.trans (val_lt_two_pow x)), ?_⟩
    rw [val_bits]
    exact ⟨ha, proper, b, hab.symm⟩
  · rintro ⟨w, _, ha, hlt, b, hb⟩
    have hb' : 1 < b := by
      by_contra! h
      have cases_b : b = 0 ∨ b = 1 := by omega
      rcases cases_b with rfl | rfl <;> simp_all
    exact ⟨val w, b, ha, hb', hb.symm⟩

end PvsNP.Units
