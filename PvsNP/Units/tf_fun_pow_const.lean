import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_pair_mul

namespace PvsNP.Units.tf_fun_pow_const

private def value (x : List Bool) : ℕ := Nat.ofDigits 2 (x.map Bool.toNat)

private theorem value_bits (n : ℕ) : value (Nat.bits n) = n := by
  have to_digit : Bool.toNat = (fun b : Bool => cond b 1 0) := by
    funext b
    cases b <;> rfl
  rw [value, to_digit, ← Nat.digits_two_eq_bits, Nat.ofDigits_digits]

end PvsNP.Units.tf_fun_pow_const

/-- Square the input word by duplication and multiply the resulting numeral by the input. -/
theorem PvsNP.Units.tf_fun_pow_const :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool =>
      Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) ^ 3)) := by
  let mulWords (p : List Bool × List Bool) :=
    Nat.bits (tf_fun_pow_const.value p.1 * tf_fun_pow_const.value p.2)
  have hid := PvsNP.Units.m2_pair_build_polytime.cpt_id
  have hdup := PvsNP.Units.m2_pair_build_polytime _ _ hid hid
  have hmul : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString mulWords :=
    PvsNP.Units.tf_fun_pair_mul
  have hsquare : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => mulWords (x, x)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun x : List Bool => (x, x)) mulWords hdup hmul
  have hp := PvsNP.Units.m2_pair_build_polytime _ _ hsquare hid
  apply PvsNP.Units.tf_fun_pair_mul.cptE (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    (fun x : List Bool => (mulWords (x, x), x)) mulWords hp hmul)
  intro x
  change Nat.bits (tf_fun_pow_const.value (Nat.bits (tf_fun_pow_const.value x * tf_fun_pow_const.value x)) *
    tf_fun_pow_const.value x) = Nat.bits (tf_fun_pow_const.value x ^ 3)
  rw [tf_fun_pow_const.value_bits]
  congr 1
  ring
