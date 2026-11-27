import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_eq_np_npc
import PvsNP.Units.m2_palindrome_in_p
import PvsNP.Units.tl_lang_cube_p

-- Built from the settled campaign units m2_p_eq_np_npc (reduces_nontrivial), m2_palindrome_in_p and tl_lang_cube_p
-- (make.fun pvsnp campaign).

namespace PvsNP.Units.m2_x_pal_cube_karp_equiv

theorem nil_cube : ([] : List Bool) ∈ ({x : List Bool | ∃ y : List Bool, x = y ++ y ++ y} : Language Bool) :=
  show ∃ y : List Bool, ([] : List Bool) = y ++ y ++ y from ⟨[], rfl⟩

theorem one_not_cube : [true] ∉ ({x : List Bool | ∃ y : List Bool, x = y ++ y ++ y} : Language Bool) := by
  intro h
  obtain ⟨y, hy⟩ := (h : ∃ y : List Bool, [true] = y ++ y ++ y)
  have hl := congrArg List.length hy
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  omega

theorem nil_pal : ([] : List Bool) ∈ ({x : List Bool | x.reverse = x} : Language Bool) :=
  show ([] : List Bool).reverse = [] from rfl

theorem tf_not_pal : [true, false] ∉ ({x : List Bool | x.reverse = x} : Language Bool) := by
  intro h
  have h' : ([true, false] : List Bool).reverse = [true, false] := h
  exact absurd h' (by decide)

end PvsNP.Units.m2_x_pal_cube_karp_equiv

theorem PvsNP.Units.m2_x_pal_cube_karp_equiv :
    PvsNP.KarpReducible ({x : List Bool | x.reverse = x} : Language Bool)
        ({x : List Bool | ∃ y : List Bool, x = y ++ y ++ y} : Language Bool) ∧
      PvsNP.KarpReducible ({x : List Bool | ∃ y : List Bool, x = y ++ y ++ y} : Language Bool)
        ({x : List Bool | x.reverse = x} : Language Bool) := by
  have _hc := Classical.em True
  exact ⟨PvsNP.Units.m2_p_eq_np_npc.reduces_nontrivial PvsNP.Units.m2_palindrome_in_p
      [] PvsNP.Units.m2_x_pal_cube_karp_equiv.nil_cube [true] PvsNP.Units.m2_x_pal_cube_karp_equiv.one_not_cube,
    PvsNP.Units.m2_p_eq_np_npc.reduces_nontrivial PvsNP.Units.tl_lang_cube_p
      [] PvsNP.Units.m2_x_pal_cube_karp_equiv.nil_pal [true, false] PvsNP.Units.m2_x_pal_cube_karp_equiv.tf_not_pal⟩
