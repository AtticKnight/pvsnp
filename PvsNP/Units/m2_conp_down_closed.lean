import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_down_closed

/-
coNP is closed downward under Karp reductions.

The argument follows lean/PEqualNP/Library/L040.lean of github.com/brilliant-hq/pequalnp-proofs at
commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License, Version 2.0): a Karp reduction
from `L₁` to `L₂` is, by the same function, a Karp reduction from `L₁ᶜ` to `L₂ᶜ` (`not_congr`).
NP is closed downward under Karp reductions, which is the settled unit
`PvsNP.Units.m2_np_down_closed`, imported above and applied here to the complements.
-/

namespace PvsNP.Units.m2_conp_down_closed

/-- A Karp reduction from `L₁` to `L₂` is, by the same function, one from `L₁ᶜ` to `L₂ᶜ`. -/
theorem karp_compl {L₁ L₂ : Language Bool} (h : PvsNP.KarpReducible L₁ L₂) :
    PvsNP.KarpReducible L₁ᶜ L₂ᶜ := by
  obtain ⟨f, hf, hfm⟩ := h
  exact ⟨f, hf, fun x => not_congr (hfm x)⟩

end PvsNP.Units.m2_conp_down_closed

/-- coNP is closed downward under Karp reductions: the reduction also reduces the complements,
and NP is closed downward (`PvsNP.Units.m2_np_down_closed`). -/
theorem PvsNP.Units.m2_conp_down_closed :
  ∀ L₁ L₂ : Language Bool, PvsNP.KarpReducible L₁ L₂ → L₂ ∈ PvsNP.coNP → L₁ ∈ PvsNP.coNP := by
  intro L₁ L₂ h h₂
  have h₂' : L₂ᶜ ∈ PvsNP.NP := h₂
  show L₁ᶜ ∈ PvsNP.NP
  exact PvsNP.Units.m2_np_down_closed L₁ᶜ L₂ᶜ
    (PvsNP.Units.m2_conp_down_closed.karp_compl h) h₂'
