import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_sat_to_naesat
import PvsNP.Units.m1_flat_to_st
import PvsNP.Units.m1_st_to_tm2
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m1_tm2_to_st
import PvsNP.Units.m1_st_to_flat

/-!
# Not-all-equal SAT is NP-hard (vendored model)

Every language in the vendored NP reduces to `SATStr` (the vendored `CookLevin.SATStr_NPhard`),
and `SATStr` reduces to not-all-equal SAT (the settled unit `PvsNP.Units.m3_sat_to_naesat`).
The two reductions are joined by composing their maps: each map is carried from the vendored
flat machines to single-tape machines (`m1_flat_to_st`), then to multi-stack machines
(`m1_st_to_tm2`), composed there (`m2_polytime_comp`), and the composite is carried back
(`m1_tm2_to_st`, `m1_st_to_flat`).
-/

namespace PvsNP.Units.m3_naesat_nphard_aux

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

end PvsNP.Units.m3_naesat_nphard_aux

theorem PvsNP.Units.m3_naesat_nphard :
    CookLevin.NPhard (fun x => ∃ a : assgn, ∀ C ∈ SATStr.cnfOf x,
      C.any (evalLiteral a) = true ∧ C.any (fun l => !evalLiteral a l) = true) := by
  intro Q hQ
  exact PvsNP.Units.m3_naesat_nphard_aux.reducesPoly_trans
    (CookLevin.SATStr_NPhard Q hQ) PvsNP.Units.m3_sat_to_naesat
