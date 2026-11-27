import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_poly_padding_iff
import PvsNP.Units.tl_lang_composite_np

-- Built from the settled campaign units m2_np_poly_padding_iff and tl_lang_composite_np (make.fun pvsnp campaign).

theorem PvsNP.Units.m2_x_composite_padded_np :
    ({s : List Bool | ∃ x : List Bool, (∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)) ∧
        s = List.replicate (x.length ^ 3) true ++ false :: x} : Language Bool) ∈ PvsNP.NP := by
  have _hc := Classical.em True
  exact (PvsNP.Units.m2_np_poly_padding_iff _ 3).1 PvsNP.Units.tl_lang_composite_np
