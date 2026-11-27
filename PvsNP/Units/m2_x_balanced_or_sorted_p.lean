import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_union
import PvsNP.Units.tl_lang_balanced_p
import PvsNP.Units.tl_lang_sorted_p

theorem PvsNP.Units.m2_x_balanced_or_sorted_p :
    ({x : List Bool | x.count true = x.count false ∨ List.SortedLE x} : Language Bool) ∈ PvsNP.P := by
  have h := PvsNP.Units.m2_p_union _ _ PvsNP.Units.tl_lang_balanced_p PvsNP.Units.tl_lang_sorted_p
  exact h
