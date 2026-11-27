import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_sat_to_doublesat
import PvsNP.Units.m1_flat_to_st
import PvsNP.Units.m1_st_to_tm2
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m1_tm2_to_st
import PvsNP.Units.m1_st_to_flat

/-!
# DOUBLE-SAT is NP-hard (vendored model)

Every language in the vendored NP reduces to `SATStr` (`CookLevin.SATStr_NPhard`), and
`SATStr` reduces to DOUBLE-SAT (the settled unit `PvsNP.Units.m3_sat_to_doublesat`).
The reductions are composed by carrying the flat machines through TM2 with the settled
bridge units `m1_flat_to_st`, `m1_st_to_tm2`, `m2_polytime_comp`, `m1_tm2_to_st`,
`m1_st_to_flat` (same argument as the settled `m3_naesat_nphard`).
-/

namespace PvsNP.Units.m3_doublesat_nphard_aux

/-- The vendored polynomial-time many-one reducibility is transitive. -/
theorem reducesPoly_trans {P Q R : List Bool → Prop}
    (hPQ : CookLevin.reducesPoly P Q) (hQR : CookLevin.reducesPoly Q R) :
    CookLevin.reducesPoly P R := by
  obtain ⟨f, t₁, M₁, ht₁, hM₁, h1₁, hc₁, hf⟩ := hPQ
  obtain ⟨g, t₂, M₂, ht₂, hM₂, h1₂, hc₂, hg⟩ := hQR
  have hf' : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f :=
    PvsNP.Units.m1_st_to_tm2 PvsNP.encodeString PvsNP.encodeString f
      (PvsNP.Units.m1_flat_to_st f t₁ M₁ ht₁ hM₁ h1₁ hc₁)
  have hg' : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g :=
    PvsNP.Units.m1_st_to_tm2 PvsNP.encodeString PvsNP.encodeString g
      (PvsNP.Units.m1_flat_to_st g t₂ M₂ ht₂ hM₂ h1₂ hc₂)
  have hgf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (g ∘ f) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      f g hf' hg'
  obtain ⟨t, M, ht, hM, h1, hc⟩ :=
    PvsNP.Units.m1_st_to_flat (g ∘ f)
      (PvsNP.Units.m1_tm2_to_st PvsNP.encodeString PvsNP.encodeString (g ∘ f) hgf)
  exact ⟨g ∘ f, t, M, ht, hM, h1, hc, fun x => (hf x).trans (hg (f x))⟩

end PvsNP.Units.m3_doublesat_nphard_aux

theorem PvsNP.Units.m3_doublesat_nphard :
    CookLevin.NPhard (fun x => ∃ a b : assgn, satisfiesCnf a (SATStr.cnfOf x) ∧ satisfiesCnf b (SATStr.cnfOf x) ∧
  ∃ C ∈ SATStr.cnfOf x, ∃ l ∈ C, evalVar a l.2 ≠ evalVar b l.2) := by
  intro Q hQ
  exact PvsNP.Units.m3_doublesat_nphard_aux.reducesPoly_trans
    (CookLevin.SATStr_NPhard Q hQ) PvsNP.Units.m3_sat_to_doublesat
