import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_p_union

/-
`m2_p_symm_diff`: `P` is closed under symmetric difference.

The symmetric difference of two languages is their union of differences,
`(L₁ ⊓ L₂ᶜ) ⊔ (L₂ ⊓ L₁ᶜ)`, and each part is closed already: the settled units `m2_p_compl`
(`P` is closed under complement), `m2_p_inter` (`P` is closed under intersection) and `m2_p_union`
(`P` is closed under union) give the three steps, and set extensionality identifies the two
languages.  Those settled units are imported, not copied.
-/

theorem PvsNP.Units.m2_p_symm_diff :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.P → L₂ ∈ PvsNP.P →
      ({x : List Bool | (x ∈ L₁ ∧ x ∉ L₂) ∨ (x ∈ L₂ ∧ x ∉ L₁)} : Language Bool) ∈ PvsNP.P := by
  intro L₁ L₂ h₁ h₂
  have hunion : (L₁ ⊓ L₂ᶜ) ⊔ (L₂ ⊓ L₁ᶜ) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_union _ _
      (PvsNP.Units.m2_p_inter L₁ L₂ᶜ h₁ (PvsNP.Units.m2_p_compl L₂ h₂))
      (PvsNP.Units.m2_p_inter L₂ L₁ᶜ h₂ (PvsNP.Units.m2_p_compl L₁ h₁))
  have heq : ({x : List Bool | (x ∈ L₁ ∧ x ∉ L₂) ∨ (x ∈ L₂ ∧ x ∉ L₁)} : Language Bool) =
      (L₁ ⊓ L₂ᶜ) ⊔ (L₂ ⊓ L₁ᶜ) := by
    ext x
    rfl
  rw [heq]
  exact hunion
