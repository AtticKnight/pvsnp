import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_union
import PvsNP.Units.tl_lang_composite_np
import PvsNP.Units.tl_lang_sum_two_squares_np

-- Built from the settled campaign units m2_np_union tl_lang_composite_np tl_lang_sum_two_squares_np (make.fun pvsnp campaign).

theorem PvsNP.Units.m2_x_composite_or_two_squares_np :
    ({x : List Bool | (∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)) ∨
        ∃ a b : ℕ, a ^ 2 + b ^ 2 = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.NP := by
  have _hc := Classical.em True
  exact PvsNP.Units.m2_np_union ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool)
    ({x : List Bool | ∃ a b : ℕ, a ^ 2 + b ^ 2 = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool)
    PvsNP.Units.tl_lang_composite_np PvsNP.Units.tl_lang_sum_two_squares_np
