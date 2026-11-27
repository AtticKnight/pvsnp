import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_succ
import PvsNP.Units.tf_fun_pow2_len
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.m2_polytime_comp

/-- Testing whether a binary numeral is below 2 to the length of another
string takes polynomial time: `v < 2 ^ m` exactly when `v + 1 ≤ 2 ^ m`, so
normalize the pair to `(bits (v + 1), bits (2 ^ m))` by the settled units
`tf_fun_succ` and `tf_fun_pow2_len` under `m2_prod_map_polytime`, then apply
the settled binary comparison `m2_binary_le_polytime`, composed by
`m2_polytime_comp`; the value of `bits n` read back in binary is `n` by
`Nat.digits_two_eq_bits` and `Nat.ofDigits_digits`. -/
theorem PvsNP.Units.m2_tm_value_lt_pow_length :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (fun p : List Bool × List Bool => decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) < 2 ^ p.2.length)) := by
  have hval : ∀ n : ℕ, Nat.ofDigits (2 : ℕ) ((Nat.bits n).map Bool.toNat) = n := by
    intro n
    have h1 : (Nat.bits n).map Bool.toNat = Nat.digits 2 n := by
      rw [Nat.digits_two_eq_bits]
      congr 1
    rw [h1, Nat.ofDigits_digits]
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => (Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + 1), Nat.bits (2 ^ p.2.length)))
    (fun q : List Bool × List Bool => decide (Nat.ofDigits (2 : ℕ) (q.1.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (q.2.map Bool.toNat)))
    (PvsNP.Units.m2_prod_map_polytime _ _ PvsNP.Units.tf_fun_succ PvsNP.Units.tf_fun_pow2_len)
    PvsNP.Units.m2_binary_le_polytime
  have hfun : (fun q : List Bool × List Bool => decide (Nat.ofDigits (2 : ℕ) (q.1.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (q.2.map Bool.toNat))) ∘
      (fun p : List Bool × List Bool => (Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + 1), Nat.bits (2 ^ p.2.length))) =
      (fun p : List Bool × List Bool => decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) < 2 ^ p.2.length)) := by
    funext p
    simp only [Function.comp_apply, hval, Nat.lt_iff_add_one_le]
  rw [hfun] at hcomp
  exact hcomp
