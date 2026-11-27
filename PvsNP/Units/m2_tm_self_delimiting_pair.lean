import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-- Writing a pair as one self-delimiting string, and reading it back, take polynomial time (TM2).
The settled unit `fr_ladner` already holds both machines:
`PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB` computes `pairB p.1 p.2`, which
unfolds to `List.replicate p.1.length true ++ false :: (p.1 ++ p.2)` (its `un n` is
`List.replicate n true`), and `cpt_unpairB` computes `unpairB`, which is the second function by
definition. Their pair encoding (`PEqualNP.Library.encodePair`) is definitionally
`PvsNP.encodePair` and their identity string encoding is definitionally `PvsNP.encodeString`. -/
theorem PvsNP.Units.m2_tm_self_delimiting_pair :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => List.replicate p.1.length true ++ false :: (p.1 ++ p.2)) ∧
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
        (fun s : List Bool => (((s.dropWhile id).tail).take (s.takeWhile id).length,
          ((s.dropWhile id).tail).drop (s.takeWhile id).length)) :=
  ⟨PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB,
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_unpairB⟩
