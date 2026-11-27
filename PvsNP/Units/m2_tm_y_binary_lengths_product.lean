import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.tf_fun_pair_mul
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_add_const

/-- The product of two lengths, in binary, takes polynomial time (TM2):
write each length in binary (`m2_unary_to_binary_polytime`, mapped over the pair
by `m2_prod_map_polytime`), then multiply the two binary numbers
(`tf_fun_pair_mul`); the two compose (`m2_polytime_comp`), and `ofDigits_bits`
says the binary value of `Nat.bits n` is `n` again. -/
theorem PvsNP.Units.m2_tm_y_binary_lengths_product :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => Nat.bits (p.1.length * p.2.length)) := by
  have hmap := PvsNP.Units.m2_prod_map_polytime
    (fun x : List Bool => Nat.bits x.length) (fun x : List Bool => Nat.bits x.length)
    PvsNP.Units.m2_unary_to_binary_polytime PvsNP.Units.m2_unary_to_binary_polytime
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => (Nat.bits p.1.length, Nat.bits p.2.length))
    (fun p : List Bool × List Bool =>
      Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    hmap PvsNP.Units.tf_fun_pair_mul
  have hfun : ((fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) ∘
      (fun p : List Bool × List Bool => (Nat.bits p.1.length, Nat.bits p.2.length))) =
      (fun p : List Bool × List Bool => Nat.bits (p.1.length * p.2.length)) := by
    funext p
    simp only [Function.comp_apply]
    rw [PvsNP.Units.tf_fun_add_const.ofDigits_bits, PvsNP.Units.tf_fun_add_const.ofDigits_bits]
  rw [hfun] at hcomp
  exact hcomp
