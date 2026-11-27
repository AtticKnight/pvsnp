import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_nphard_iff_compl_conphard

theorem karp_compl {A B : Language Bool} (h : PvsNP.KarpReducible A B) :
    PvsNP.KarpReducible Aᶜ Bᶜ := by
  obtain ⟨f, hf, hfm⟩ := h
  refine ⟨f, hf, fun x => ?_⟩
  have hx := hfm x
  constructor
  · intro h1 h2
    exact h1 (hx.mpr h2)
  · intro h1
    by_contra h2
    have hA : x ∈ A := by by_contra hc; exact h2 hc
    exact h1 (hx.mp hA)

end PvsNP.Units.m2_nphard_iff_compl_conphard

theorem PvsNP.Units.m2_nphard_iff_compl_conphard :
    ∀ L : Language Bool, PvsNP.NPHard L ↔ ∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' Lᶜ := by
  intro L
  constructor
  · intro hHard L' hL'
    have h := PvsNP.Units.m2_nphard_iff_compl_conphard.karp_compl (hHard L'ᶜ hL')
    rwa [compl_compl] at h
  · intro hHard L' hL'
    have hco : L'ᶜ ∈ PvsNP.coNP := by
      show L'ᶜᶜ ∈ PvsNP.NP
      rwa [compl_compl]
    have h := PvsNP.Units.m2_nphard_iff_compl_conphard.karp_compl (hHard L'ᶜ hco)
    rwa [compl_compl, compl_compl] at h
