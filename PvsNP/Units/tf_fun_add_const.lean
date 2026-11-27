import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.tf_fun_pair_add

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-- Supply the least-significant-first encoding of five as the second argument to binary addition. -/
theorem PvsNP.Units.tf_fun_add_const :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 5)) := by
  have p := PvsNP.Units.m2_pair_build_polytime id (fun _ => [true, false, true])
    cpt_id (cpt_const [true, false, true])
  have h := PvsNP.Units.m2_pair_build_polytime.cpt_comp p PvsNP.Units.tf_fun_pair_add
  have e : Nat.ofDigits (2 : ℕ) ([true, false, true].map Bool.toNat) = 5 := by decide
  simpa only [id_eq, e] using h
