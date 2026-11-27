import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_tm_binary_half_double

namespace PvsNP.Units.m2_tm_lsb_msb_convert

/-- First map: reverse the string, then strip the leading zeros of the numeral it writes,
which is the bits of the value of the reversed string. -/
theorem cpt_first :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.reverse.map Bool.toNat))) := by
  have hRev : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) List.reverse :=
    PvsNP.Units.m2_reverse_polytime
  have h := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hRev
    PvsNP.Units.m2_tm_binary_half_double.cpt_stripLSB
  refine PvsNP.Units.m2_tm_binary_half_double.cptE h (fun x => ?_)
  simp only [Function.comp_apply, PvsNP.Units.m2_tm_binary_half_double.stripLSB_eq_bits]
  rfl

/-- Second map: strip the leading zeros of the numeral the string writes, then reverse the
resulting bits, which is the reverse of the bits of the value of the string. -/
theorem cpt_second :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => (Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))).reverse) := by
  have hRev : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) List.reverse :=
    PvsNP.Units.m2_reverse_polytime
  have h := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
    PvsNP.Units.m2_tm_binary_half_double.cpt_stripLSB hRev
  refine PvsNP.Units.m2_tm_binary_half_double.cptE h (fun x => ?_)
  simp only [Function.comp_apply, PvsNP.Units.m2_tm_binary_half_double.stripLSB_eq_bits]
  rfl

end PvsNP.Units.m2_tm_lsb_msb_convert

theorem PvsNP.Units.m2_tm_lsb_msb_convert :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.reverse.map Bool.toNat))) ∧
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => (Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat))).reverse) := by
  exact ⟨PvsNP.Units.m2_tm_lsb_msb_convert.cpt_first,
    PvsNP.Units.m2_tm_lsb_msb_convert.cpt_second⟩
