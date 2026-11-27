import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m1_flat_to_st
import PvsNP.Units.m1_st_to_tm2
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m1_tm2_to_st
import PvsNP.Units.m1_st_to_flat

/-!
# m3_npcomplete_of_sat_reduction

Hardness comes from the vendored `CookLevin.SATStr_NPhard`; the reductions are composed by
round-tripping the flat machines through TM2 using the settled bridge units
`m1_flat_to_st`, `m1_st_to_tm2`, `m2_polytime_comp`, `m1_tm2_to_st`, `m1_st_to_flat`.
-/

namespace PvsNP.Units.m3_npcomplete_of_sat_reduction

/-- Vendored polynomial-time many-one reductions compose. -/
theorem reducesPoly_trans (A B C : List Bool → Prop)
    (h₁ : CookLevin.reducesPoly A B) (h₂ : CookLevin.reducesPoly B C) :
    CookLevin.reducesPoly A C := by
  obtain ⟨f, t₁, M₁, ht₁, hv₁, h1₁, hc₁, hf⟩ := h₁
  obtain ⟨g, t₂, M₂, ht₂, hv₂, h1₂, hc₂, hg⟩ := h₂
  have sf := PvsNP.Units.m1_st_to_tm2 _ _ _ (PvsNP.Units.m1_flat_to_st f t₁ M₁ ht₁ hv₁ h1₁ hc₁)
  have sg := PvsNP.Units.m1_st_to_tm2 _ _ _ (PvsNP.Units.m1_flat_to_st g t₂ M₂ ht₂ hv₂ h1₂ hc₂)
  have hcomp := PvsNP.Units.m2_polytime_comp _ _ _ f g sf sg
  obtain ⟨t, M, ht, hv, h1, hc⟩ :=
    PvsNP.Units.m1_st_to_flat (g ∘ f) (PvsNP.Units.m1_tm2_to_st _ _ _ hcomp)
  exact ⟨g ∘ f, t, M, ht, hv, h1, hc, fun x => (hf x).trans (hg (f x))⟩

end PvsNP.Units.m3_npcomplete_of_sat_reduction

theorem PvsNP.Units.m3_npcomplete_of_sat_reduction :
    ∀ Q : List Bool → Prop, CookLevin.inNP Q → CookLevin.reducesPoly SATStr Q → CookLevin.NPcomplete Q := by
  intro Q hQ hred
  exact ⟨fun R hR => PvsNP.Units.m3_npcomplete_of_sat_reduction.reducesPoly_trans R SATStr Q
    (CookLevin.SATStr_NPhard R hR) hred, hQ⟩
