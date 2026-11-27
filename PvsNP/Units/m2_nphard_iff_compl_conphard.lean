import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_compl_iff

/-- Complementing the source exchanges NP and coNP, while the same reduction complements the target. -/
theorem PvsNP.Units.m2_nphard_iff_compl_conphard :
    ∀ L : Language Bool, PvsNP.NPHard L ↔ ∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' Lᶜ := by
  intro L
  constructor
  · intro hard A hA
    have r := hard Aᶜ hA
    simpa only [compl_compl] using (PvsNP.Units.m2_karp_compl_iff Aᶜ L).1 r
  · intro hard A hA
    apply (PvsNP.Units.m2_karp_compl_iff A L).2
    apply hard Aᶜ
    change Aᶜᶜ ∈ PvsNP.NP
    simpa only [compl_compl] using hA
