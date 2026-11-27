import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_np_down_closed

theorem PvsNP.Units.m2_npc_iff_karp_equiv_npc :
    ∀ L₀ : Language Bool, PvsNP.NPComplete L₀ → ∀ L : Language Bool,
      PvsNP.NPComplete L ↔ PvsNP.KarpReducible L L₀ ∧ PvsNP.KarpReducible L₀ L := by
  intro L₀ hL₀ L
  constructor
  · intro hL
    exact ⟨hL₀.2 L hL.1, hL.2 L₀ hL₀.1⟩
  · rintro ⟨hLL₀, hL₀L⟩
    refine ⟨PvsNP.Units.m2_np_down_closed L L₀ hLL₀ hL₀.1, fun L' hL' => ?_⟩
    rcases hL₀.2 L' hL' with ⟨f, hf, hfx⟩
    rcases hL₀L with ⟨g, hg, hgx⟩
    exact ⟨g ∘ f,
      PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
        f g hf hg,
      fun x => (hfx x).trans (hgx (f x))⟩
