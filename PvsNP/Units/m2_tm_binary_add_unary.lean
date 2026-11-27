import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.tf_fun_pair_add
import PvsNP.Units.tf_fun_pair_div

/-- Convert the right word's length to binary, then feed both binary operands to the adder. -/
theorem PvsNP.Units.m2_tm_binary_add_unary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + p.2.length)) := by
  have right : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits p.2.length) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      (fun p : List Bool × List Bool => p.2) (fun w : List Bool => w.length.bits)
      PvsNP.Units.m2_pair_split_polytime.2.1 PvsNP.Units.m2_unary_to_binary_polytime
  have prepare := PvsNP.Units.m2_tm_pair_fork_polytime _ _
    PvsNP.Units.m2_pair_split_polytime.1 right
  have result := PvsNP.Units.m2_polytime_comp _ _ _ _ _ prepare PvsNP.Units.tf_fun_pair_add
  have decode (n : ℕ) : Nat.ofDigits (2 : ℕ) (n.bits.map Bool.toNat) = n :=
    PvsNP.Units.tf_fun_pair_div.val_bits n
  simpa only [Function.comp_def, decode] using result
