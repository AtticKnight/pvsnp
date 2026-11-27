import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_len_le_polytime

/-- The campaign's pair encoding (Mathlib's `encodingProd` of two `encodingList Bool`) is the
upstream library's `encodePair`: `x` tagged left, then `w` tagged right. -/
theorem encodePair_eq :
    PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
  funext p
  rfl

end PvsNP.Units.m2_len_le_polytime

/-- Deciding `x.length ≤ w.length` is polynomial-time on TM2: swap the pair (`cpt_swap`), then run
the settled comparison machine `LenCmp.lenLE_polyTime`, which answers `w'.length ≤ x'.length`. -/
theorem PvsNP.Units.m2_len_le_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length)) := by
  rw [PvsNP.Units.m2_len_le_polytime.encodePair_eq]
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_swap
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.LenCmp.lenLE_polyTime
