import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.m2_tm_pair_bool_combine

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_binary_lt

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

theorem binary_lt_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
  have hle : ComputableInPolyTime encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) :=
    PvsNP.Units.m2_binary_le_polytime
  have hswap : ComputableInPolyTime encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat))) :=
    cpt_comp cpt_swap hle
  have hnot := PvsNP.Units.m2_tm_pair_bool_combine (fun b _ => !b) _ _ hswap hswap
  have heq : (fun p : List Bool × List Bool =>
        !decide (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat))) =
      (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) := by
    funext p
    apply Bool.eq_iff_iff.2
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, not_le]
  rwa [heq] at hnot

end PvsNP.Units.m2_tm_binary_lt

theorem PvsNP.Units.m2_tm_binary_lt :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))) :=
  PvsNP.Units.m2_tm_binary_lt.binary_lt_polytime
