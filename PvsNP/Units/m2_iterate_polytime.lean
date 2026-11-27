import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.fr_ladner

/-
The iterating machine is the settled unit `fr_ladner`'s
`PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.Iter.iter_polyTime`, adapted from
github.com/brilliant-hq/pequalnp-proofs at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its file
lean/PEqualNP/Library/Machines/Iter.lean.

The campaign's encodings agree with the ones that lemma uses, by definition:
`PvsNP.encodeString` is `(Computability.encodingList Bool).encode`, whose encode is `id`,
and `PvsNP.encodePair` is `(Computability.encodingProd _ _).encode`, which on a pair is
the two lists tagged `Sum.inl` and `Sum.inr`, exactly
`PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair`.
-/

namespace PvsNP.Units.m2_iterate_polytime

end PvsNP.Units.m2_iterate_polytime

/-- Iterating a length-bounded polynomial-time map |w| times is polynomial-time (TM2). -/
theorem PvsNP.Units.m2_iterate_polytime :
    ∀ (g : List Bool → List Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g →
        (∀ y : List Bool, (g y).length ≤ y.length + k) →
          PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
            (fun p : List Bool × List Bool => g^[p.2.length] p.1) := by
  intro g k hg hk
  obtain ⟨c⟩ := hg
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.Iter.iter_polyTime g c k hk
