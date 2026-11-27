import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_binary_half_double
import PvsNP.Units.tf_fun_zip_with

namespace PvsNP.Units.tf_fun_pair_land

private def value (x : List Bool) : ℕ := Nat.ofDigits 2 (x.map Bool.toNat)

private theorem value_cons (b : Bool) (x : List Bool) :
    value (b :: x) = Nat.bit b (value x) := by
  cases b <;> simp [value, Nat.ofDigits_cons, Nat.bit_val] <;> omega

private theorem value_and (x y : List Bool) :
    value (List.zipWith (fun a b : Bool => a && b) x y) = value x &&& value y := by
  induction x generalizing y with
  | nil => simp [value]
  | cons a xs ih =>
    cases y with
    | nil => simp [value]
    | cons b ys =>
      change value ((a && b) :: List.zipWith (fun u v : Bool => u && v) xs ys) =
        value (a :: xs) &&& value (b :: ys)
      rw [value_cons, value_cons a, value_cons b, Nat.land_bit, ih]

end PvsNP.Units.tf_fun_pair_land

/-- AND each shared low-order bit and strip the trailing zero bits.
An absent high-order bit equals zero, so truncating the zip loses no set bit. -/
theorem PvsNP.Units.tf_fun_pair_land :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) &&& Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
  have canonical : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun xs : List Bool => Nat.bits (tf_fun_pair_land.value xs)) :=
    PvsNP.Units.m2_tm_binary_half_double.cptE PvsNP.Units.m2_tm_binary_half_double.cpt_stripLSB
      PvsNP.Units.m2_tm_binary_half_double.stripLSB_eq_bits
  apply PvsNP.Units.m2_tm_binary_half_double.cptE
    (PvsNP.Units.m2_polytime_comp _ _ _ _ _ PvsNP.Units.tf_fun_zip_with canonical)
  intro p
  exact congrArg Nat.bits (tf_fun_pair_land.value_and p.1 p.2)
