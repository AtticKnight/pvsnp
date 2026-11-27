import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-!
`NP ⊆ NEXP` on Mathlib's TM2: every NP language has a polynomial-time verifier
whose certificates are bounded by `2 ^ (n ^ k) + k`.

The proof goes through the settled unit `fr_ladner`: its bridge `NP_iff` carries
`L ∈ PvsNP.NP` over to the upstream `PEqualNP.Library.NP`, its `L048` proves
`NP ⊆ NEXP` upstream (via `L045`, which hands back a verifier that accepts no
certificate past its polynomial bound, and `polynomial_le_two_pow_pow_add`,
which bounds that polynomial by `2 ^ (n ^ k) + k`), and the upstream
`DecidableInPolyTime` unfolds to the campaign's `PvsNP.PolyTimeComputable`
with the same encodings, so the verifier it returns is the one the posted
statement asks for.
-/

namespace PvsNP.Units.m2_np_subset_nexp

/-- The posted statement, proved inside the unit's namespace. -/
theorem aux :
    ∀ L ∈ PvsNP.NP, ∃ (V : List Bool × List Bool → Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ L ↔
          ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true := by
  intro L hL
  have hL' : L ∈ PvsNP.Units.fr_ladner.PEqualNP.Library.NP :=
    (PvsNP.Units.fr_ladner.NP_iff L).1 hL
  obtain ⟨R, k, hR, hmem⟩ :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.L048 hL'
  obtain ⟨V, hf, hV⟩ := hR
  exact ⟨V, k, hV, fun x =>
    (hmem x).trans (exists_congr fun w => and_congr_right fun _ => hf (x, w))⟩

end PvsNP.Units.m2_np_subset_nexp

theorem PvsNP.Units.m2_np_subset_nexp :
    ∀ L ∈ PvsNP.NP, ∃ (V : List Bool × List Bool → Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ L ↔
          ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true :=
  PvsNP.Units.m2_np_subset_nexp.aux
