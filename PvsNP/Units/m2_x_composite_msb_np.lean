import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.tl_lang_composite_np

theorem PvsNP.Units.m2_x_composite_msb_np :
    ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.reverse.map Bool.toNat)} : Language Bool) ∈ PvsNP.NP := by
  exact m2_np_down_closed _ _ ⟨List.reverse, m2_reverse_polytime, fun _ => Iff.rfl⟩ tl_lang_composite_np
