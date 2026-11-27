import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

theorem PvsNP.Units.m2_p_ne_np_ladner_props :
    PvsNP.P ≠ PvsNP.NP → ∃ L ∈ PvsNP.NP, L ∉ PvsNP.P ∧ (∃ y : List Bool, y ∈ L) ∧ (∃ z : List Bool, z ∉ L) ∧
      ∀ L₀ : Language Bool, PvsNP.NPComplete L₀ → ¬ PvsNP.KarpReducible L₀ L := by
  intro hne
  have hex : ∃ L ∈ PvsNP.NP, L ∉ PvsNP.P := by
    by_contra h
    push Not at h
    exact hne (Set.Subset.antisymm PvsNP.Units.m2_p_subset_np h)
  obtain ⟨L, hNP, hNotP, hNotNPC⟩ := PvsNP.Units.fr_ladner hex
  refine ⟨L, hNP, hNotP, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    apply hNotP
    have hempty : L = (∅ : Set (List Bool)) := Set.eq_empty_iff_forall_notMem.mpr h
    rw [hempty]
    exact PvsNP.Units.m2_p_trivial.1
  · by_contra h
    push Not at h
    apply hNotP
    have huniv : L = (Set.univ : Set (List Bool)) := Set.eq_univ_iff_forall.mpr h
    rw [huniv]
    exact PvsNP.Units.m2_p_trivial.2
  · intro L₀ hNPC ⟨g, hg, hgm⟩
    apply hNotNPC
    refine ⟨hNP, fun A hA => ?_⟩
    obtain ⟨f, hf, hfm⟩ := hNPC.2 A hA
    exact ⟨g ∘ f, PvsNP.Units.m2_polytime_comp _ _ _ f g hf hg, fun x => (hfm x).trans (hgm (f x))⟩
