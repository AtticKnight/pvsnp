import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_refl
import PvsNP.Units.m2_karp_trans

/-- Reducing to each other is an equivalence relation on languages (TM2). -/
theorem PvsNP.Units.m2_karp_equiv_equivalence :
    Equivalence (fun L₁ L₂ : Language Bool =>
      PvsNP.KarpReducible L₁ L₂ ∧ PvsNP.KarpReducible L₂ L₁) :=
  ⟨fun L => ⟨PvsNP.Units.m2_karp_refl L, PvsNP.Units.m2_karp_refl L⟩,
   fun h => ⟨h.2, h.1⟩,
   fun h₁ h₂ => ⟨PvsNP.Units.m2_karp_trans _ _ _ h₁.1 h₂.1,
     PvsNP.Units.m2_karp_trans _ _ _ h₂.2 h₁.2⟩⟩
