import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_self_append
import PvsNP.Units.m2_unary_to_binary_polytime

set_option autoImplicit false

/-!
`x ++ x` has length `2 * x.length`, so the binary form of `2 * x.length` is the settled
`m2_unary_to_binary_polytime` after the settled `tf_fun_self_append`.
-/

theorem PvsNP.Units.m2_tm_length_double_binary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => Nat.bits (2 * x.length)) := by
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x ++ x) (fun y : List Bool => Nat.bits y.length)
    PvsNP.Units.tf_fun_self_append PvsNP.Units.m2_unary_to_binary_polytime
  have e : ((fun y : List Bool => Nat.bits y.length) ∘ (fun x : List Bool => x ++ x)) =
      (fun x : List Bool => Nat.bits (2 * x.length)) := by
    funext x
    first
    | (simp only [Function.comp_apply, List.length_append, two_mul])
    | (show Nat.bits (x ++ x).length = Nat.bits (2 * x.length)
       rw [List.length_append, two_mul])
  first
  | (rw [e] at h; exact h)
  | exact e ▸ h
