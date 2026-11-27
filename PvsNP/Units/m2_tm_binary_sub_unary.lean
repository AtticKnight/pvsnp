import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_tm_binary_half_double
import PvsNP.Units.tf_fun_pair_div
import PvsNP.Units.tf_fun_pred

namespace PvsNP.Units.m2_tm_binary_sub_unary

open PvsNP.Units.tf_fun_pair_div (val val_bits val_lt)
open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def decrement (word : List Bool) : List Bool := (val word - 1).bits

theorem iterate_decrement (n k : ℕ) :
    (decrement^[k]) n.bits = (n - k).bits := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    change (val (n - k).bits - 1).bits = (n - (k + 1)).bits
    rw [val_bits]
    exact congrArg Nat.bits (by omega)

theorem subtract_length :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => (val p.1 - p.2.length).bits) := by
  have step : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString decrement :=
    PvsNP.Units.tf_fun_pred
  have bound (w : List Bool) : (decrement w).length ≤ w.length + 0 := by
    change (val w - 1).bits.length ≤ w.length + 0
    rw [Nat.add_zero, Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (lt_of_le_of_lt (Nat.sub_le _ _) (val_lt w))
  have init : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (val (unpairB s).1).bits) :=
    PvsNP.Units.m2_tm_binary_half_double.cptE
      (PvsNP.Units.tf_fun_pred.T_poly (cpt_unpairB1_1 cpt_id))
      (fun s => (PvsNP.Units.tf_fun_pred.bits_val (unpairB s).1).symm)
  have loop := cpt_iterGrow step 0 bound (cpt_unpairB2_1 cpt_id) init
  apply PvsNP.Units.m2_tm_binary_half_double.cptE (cpt_comp cpt_pairB loop)
  rintro ⟨x, y⟩
  change (decrement^[(unpairB (pairB x y)).2.length])
    (val (unpairB (pairB x y)).1).bits = (val x - y.length).bits
  rw [unpairB_pairB]
  exact iterate_decrement _ _

end PvsNP.Units.m2_tm_binary_sub_unary

/-- Unary subtraction needs one non-growing saturating predecessor step per bit of the right word. -/
theorem PvsNP.Units.m2_tm_binary_sub_unary :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) - p.2.length)) :=
  PvsNP.Units.m2_tm_binary_sub_unary.subtract_length
