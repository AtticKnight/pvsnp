import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_palindrome_in_p

-- Built from the settled campaign unit m2_palindrome_in_p (make.fun pvsnp campaign).

namespace PvsNP.Units.m2_x_self_append_pal_p

theorem pal_eq :
    ({x : List Bool | (x ++ x).reverse = x ++ x} : Language Bool) =
      ({x : List Bool | x.reverse = x} : Language Bool) := by
  ext x
  show (x ++ x).reverse = x ++ x ↔ x.reverse = x
  rw [List.reverse_append]
  constructor
  · intro h
    exact (List.append_inj h (by simp)).1
  · intro h
    rw [h]

end PvsNP.Units.m2_x_self_append_pal_p

theorem PvsNP.Units.m2_x_self_append_pal_p :
    ({x : List Bool | (x ++ x).reverse = x ++ x} : Language Bool) ∈ PvsNP.P := by
  have _hc := Classical.em True
  rw [PvsNP.Units.m2_x_self_append_pal_p.pal_eq]
  exact PvsNP.Units.m2_palindrome_in_p
