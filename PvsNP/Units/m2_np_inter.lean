import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_verifier_normal

theorem PvsNP.Units.m2_np_inter :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.NP → L₂ ∈ PvsNP.NP → L₁ ⊓ L₂ ∈ PvsNP.NP :=
  PvsNP.Units.m2_np_verifier_normal.np_inter
