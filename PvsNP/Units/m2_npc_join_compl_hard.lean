import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_karp_trans

theorem PvsNP.Units.m2_npc_join_compl_hard :
    ∀ L : Language Bool, PvsNP.NPComplete L →
      PvsNP.NPHard ({x : List Bool | (∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ Lᶜ, x = true :: y)} : Language Bool) ∧
        ∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' ({x : List Bool | (∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ Lᶜ, x = true :: y)} : Language Bool) := by
  intro L hL
  obtain ⟨hNP, hHard⟩ := hL
  have hside := PvsNP.Units.m2_join_karp_sides L Lᶜ
  constructor
  · intro L' hL'
    exact PvsNP.Units.m2_karp_trans L' L _ (hHard L' hL') hside.1
  · intro L' hL'
    obtain ⟨f, hf, hfm⟩ := hHard L'ᶜ hL'
    have hcomp : PvsNP.KarpReducible L' Lᶜ :=
      ⟨f, hf, fun x => by
        have h := hfm x
        constructor
        · intro hx hfx
          exact h.mpr hfx hx
        · intro hx
          by_contra hx'
          exact hx (h.mp hx')⟩
    exact PvsNP.Units.m2_karp_trans L' Lᶜ _ hcomp hside.2
