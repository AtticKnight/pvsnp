import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tl_lang_composite_np

set_option autoImplicit false

/-- The strings whose binary value is not composite are in coNP (TM2):
    the complement is the composites, which are in NP by the settled unit
    `tl_lang_composite_np`. -/
theorem PvsNP.Units.m2_x_not_composite_conp :
    ({x : List Bool | ¬ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.coNP := by
  have hcomp : ({x : List Bool | ¬ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool)ᶜ
      = {x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  show ({x : List Bool | ¬ ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool)ᶜ ∈ PvsNP.NP
  rw [hcomp]
  exact PvsNP.Units.tl_lang_composite_np
