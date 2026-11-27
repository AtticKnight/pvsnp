import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-- Multiplying two lengths in unary is polynomial-time (TM2).

The settled unit `fr_ladner` already holds this multiplication machine:
`PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_mulU` proves the same
function computable in polynomial time, with the campaign's own pair encoding
(`PEqualNP.Library.encodePair`, definitionally `PvsNP.encodePair`) and the
identity string encoding (definitionally `PvsNP.encodeString`, as the bridge
theorems in `fr_ladner` show), and `mulU p.1 p.2` unfolds to
`List.replicate (p.1.length * p.2.length) true`. -/
theorem PvsNP.Units.m2_mul_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_mulU
