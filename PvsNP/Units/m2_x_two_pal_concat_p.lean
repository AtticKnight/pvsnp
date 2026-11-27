import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.m2_palindrome_in_p

import PvsNP.Units.m2_p_concat

namespace PvsNP.Units.m2_x_two_pal_concat_p

/-- Two palindromes one after the other are the concatenation of the palindrome language with
itself, which is in P by the settled concatenation unit. -/
theorem two_pal_concat :
    ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u.reverse = u ∧ v.reverse = v} :
      Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.m2_p_concat _ _ PvsNP.Units.m2_palindrome_in_p
    PvsNP.Units.m2_palindrome_in_p

end PvsNP.Units.m2_x_two_pal_concat_p

theorem PvsNP.Units.m2_x_two_pal_concat_p :
    ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u.reverse = u ∧ v.reverse = v} :
      Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.m2_x_two_pal_concat_p.two_pal_concat
