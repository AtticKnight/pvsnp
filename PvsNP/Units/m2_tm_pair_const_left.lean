import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp (Apache License
2.0), which this file imports: its machines are those of github.com/brilliant-hq/pequalnp-proofs
at commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0).
-/

/-- Pairing a fixed string with the input is polynomial-time (TM2): the constant and the
identity, run side by side. -/
theorem PvsNP.Units.m2_tm_pair_const_left :
    ∀ w : List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (w, x)) :=
  fun w => PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_pair (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const w) PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
