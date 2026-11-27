import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_palindrome_in_p

theorem PvsNP.Units.m2_x_not_pal_p :
    ({x : List Bool | x.reverse ≠ x} : Language Bool) ∈ PvsNP.P := by
  -- The non-palindromes are exactly the complement of the palindromes.
  have h : ({x : List Bool | x.reverse ≠ x} : Language Bool)
      = ({x : List Bool | x.reverse = x} : Language Bool)ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, ne_eq]
  rw [h]
  exact PvsNP.Units.m2_p_compl _ PvsNP.Units.m2_palindrome_in_p
