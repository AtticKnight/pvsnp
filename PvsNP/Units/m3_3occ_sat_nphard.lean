import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_sat_to_3occ_sat
import PvsNP.Units.m1_flat_to_st
import PvsNP.Units.m1_st_to_tm2
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m1_tm2_to_st
import PvsNP.Units.m1_st_to_flat

-- Adapted from PvsNP/Units/m3_naesat_nphard.lean of https://github.com/makedotfun/pvsnp
-- (Apache License, Version 2.0), contributor mevlanayalcin,
-- commit f3b84be5652788c07d6b067c9a274fa24b53368a (2026-11-27).
-- The `reducesPoly_trans` helper below is that file's transitivity argument,
-- reused verbatim except for the namespace rename; the closing theorem is new
-- for this unit. This file also uses the settled unit
-- PvsNP.Units.m3_sat_to_3occ_sat (contributor rappejet07,
-- commit fa8857730a0690422ef95e657a60b195713633f1, Apache-2.0).
-- The settled unit PvsNP.Units.m3_reduces_poly_trans (settled 2026-11-27 by
-- jolly-kestrel-38-9387) has no GitHub commit, so its file is not in the
-- campaign tree; transitivity is therefore proved inline here instead.

namespace PvsNP.Units.m3_3occ_sat_nphard_aux

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

end PvsNP.Units.m3_3occ_sat_nphard_aux

/-- SAT with each variable in at most three literals is NP-hard (vendored model). -/
theorem PvsNP.Units.m3_3occ_sat_nphard :
    CookLevin.NPhard (fun x => (∀ v : var, ((SATStr.cnfOf x).flatten.countP (fun l => l.2 == v)) ≤ 3) ∧
      SAT (SATStr.cnfOf x)) := by
  intro Q hQ
  exact PvsNP.Units.m3_3occ_sat_nphard_aux.reducesPoly_trans
    (CookLevin.SATStr_NPhard Q hQ) PvsNP.Units.m3_sat_to_3occ_sat
