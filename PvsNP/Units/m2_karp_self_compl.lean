import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_compl_iff
import PvsNP.Units.m2_np_down_closed

/-- Complementing both endpoints reverses this particular reduction. Pull NP membership back along it. -/
theorem PvsNP.Units.m2_karp_self_compl :
    ∀ L : Language Bool, (PvsNP.KarpReducible L Lᶜ ↔ PvsNP.KarpReducible Lᶜ L) ∧
  (PvsNP.KarpReducible L Lᶜ → L ∈ PvsNP.NP → L ∈ PvsNP.NP ∩ PvsNP.coNP) := by
  intro L
  have eqv : PvsNP.KarpReducible L Lᶜ ↔ PvsNP.KarpReducible Lᶜ L := by
    simpa only [compl_compl] using PvsNP.Units.m2_karp_compl_iff L Lᶜ
  exact ⟨eqv, fun r h => ⟨h, PvsNP.Units.m2_np_down_closed Lᶜ L (eqv.1 r) h⟩⟩
