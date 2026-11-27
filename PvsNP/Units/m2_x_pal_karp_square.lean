import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_palindrome_in_p
import PvsNP.Units.m2_p_reduces_nontrivial

theorem PvsNP.Units.m2_x_pal_karp_square : PvsNP.KarpReducible ({x : List Bool | x.reverse = x} : Language Bool)
  ({x : List Bool | ∃ y : List Bool, x = y ++ y} : Language Bool) := by
  refine PvsNP.Units.m2_p_reduces_nontrivial _ _ PvsNP.Units.m2_palindrome_in_p ?_ ?_
  · exact ⟨[], [], rfl⟩
  · refine ⟨[true], ?_⟩
    rintro ⟨y, hy⟩
    have hlen := congrArg List.length hy
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
