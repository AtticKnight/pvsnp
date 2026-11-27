import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tl_lang_composite_np
import PvsNP.Units.tl_lang_balanced_p
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_union

theorem PvsNP.Units.m2_x_composite_or_balanced_np :
    ({x : List Bool | (∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)) ∨
        x.count true = x.count false} : Language Bool) ∈ PvsNP.NP := by
  have hcomp := PvsNP.Units.tl_lang_composite_np
  have hbal : ({x : List Bool | x.count true = x.count false} : Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np PvsNP.Units.tl_lang_balanced_p
  have hunion := PvsNP.Units.m2_np_union _ _ hcomp hbal
  have heq : ({x : List Bool | (∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)) ∨
        x.count true = x.count false} : Language Bool) =
      ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ⊔
      ({x : List Bool | x.count true = x.count false} : Language Bool) := by
    ext x
    simp
  rw [heq]
  exact hunion
