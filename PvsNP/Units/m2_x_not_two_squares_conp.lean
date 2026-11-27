import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tl_lang_sum_two_squares_np

theorem PvsNP.Units.m2_x_not_two_squares_conp :
    ({x : List Bool | ∀ a b : ℕ, a ^ 2 + b ^ 2 ≠ Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.coNP := by
  classical
  have heq : ({x : List Bool | ∀ a b : ℕ, a ^ 2 + b ^ 2 ≠ Nat.ofDigits 2 (x.map Bool.toNat)} : Language Bool)ᶜ =
      {x : List Bool | ∃ a b : ℕ, a ^ 2 + b ^ 2 = Nat.ofDigits 2 (x.map Bool.toNat)} := by
    ext x
    change (¬ ∀ a b : ℕ, a ^ 2 + b ^ 2 ≠ _) ↔ ∃ a b : ℕ, a ^ 2 + b ^ 2 = _
    simp
  exact (congrArg (fun L : Language Bool => L ∈ PvsNP.NP) heq).mpr PvsNP.Units.tl_lang_sum_two_squares_np
