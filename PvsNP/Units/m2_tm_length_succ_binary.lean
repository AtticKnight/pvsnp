import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.tf_fun_prepend_all

/-- Writing the length of a string plus one in binary takes polynomial time (TM2):
first prepend `[true]` to the input, which grows its length by one, then write that
length in binary. Both steps are polynomial-time by settled units, and polynomial-time
computable functions compose. -/
theorem PvsNP.Units.m2_tm_length_succ_binary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (x.length + 1)) := by
  have hPrepend := PvsNP.Units.tf_fun_prepend_all [true]
  have hBinary := PvsNP.Units.m2_unary_to_binary_polytime
  have hComp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => [true] ++ x)
    (fun x : List Bool => Nat.bits x.length) hPrepend hBinary
  have hEq : (fun x : List Bool => Nat.bits x.length) ∘ (fun x : List Bool => [true] ++ x)
      = fun x : List Bool => Nat.bits (x.length + 1) := by
    funext x
    simp only [Function.comp_apply, List.cons_append, List.nil_append, List.length_cons]
  rw [hEq] at hComp
  exact hComp
