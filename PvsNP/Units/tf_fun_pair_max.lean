import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_binary_half_double
import PvsNP.Units.m2_tm_pair_ite_polytime

/-- Select the larger numeral by binary comparison and remove redundant high zeroes. -/
theorem PvsNP.Units.tf_fun_pair_max :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => Nat.bits (max (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat)) (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))) := by
  let value (xs : List Bool) := Nat.ofDigits (2 : ℕ) (xs.map Bool.toNat)
  have canonical : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun xs : List Bool => Nat.bits (value xs)) :=
    PvsNP.Units.m2_tm_binary_half_double.cptE
      PvsNP.Units.m2_tm_binary_half_double.cpt_stripLSB
      PvsNP.Units.m2_tm_binary_half_double.stripLSB_eq_bits
  have left : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits (value p.1)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ PvsNP.Units.m2_pair_split_polytime.1 canonical
  have right : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits (value p.2)) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _ PvsNP.Units.m2_pair_split_polytime.2.1 canonical
  have choose := PvsNP.Units.m2_tm_pair_ite_polytime
    (fun p : List Bool × List Bool => decide (value p.1 ≤ value p.2))
    _ _ PvsNP.Units.m2_binary_le_polytime right left
  apply PvsNP.Units.m2_tm_binary_half_double.cptE choose
  intro p
  change (if decide (value p.1 ≤ value p.2) = true then Nat.bits (value p.2)
    else Nat.bits (value p.1)) = Nat.bits (max (value p.1) (value p.2))
  by_cases h : value p.1 ≤ value p.2
  · simp [h, max_eq_right h]
  · simp [h, max_eq_left (le_of_lt (lt_of_not_ge h))]
