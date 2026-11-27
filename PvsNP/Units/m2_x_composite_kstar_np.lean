import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_kstar
import PvsNP.Units.tl_lang_composite_np

theorem PvsNP.Units.m2_x_composite_kstar_np :
    @KStar.kstar (Language Bool) _ ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.NP := by
  exact PvsNP.Units.m2_np_kstar _ PvsNP.Units.tl_lang_composite_np
