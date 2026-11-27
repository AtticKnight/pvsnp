import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.tf_fun_self_append
import PvsNP.Units.m2_polytime_comp

/-
Closes m2_x_self_append_reverse_polytime: reversing a doubled string
(`(x ++ x).reverse`) is polynomial-time. Double the string (settled
`tf_fun_self_append`), then reverse it (settled `m2_reverse_polytime`),
composed (settled `m2_polytime_comp`).
-/

set_option autoImplicit false

theorem PvsNP.Units.m2_x_self_append_reverse_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => (x ++ x).reverse) := by
  have hRev : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.reverse) := PvsNP.Units.m2_reverse_polytime
  have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => x ++ x) List.reverse
    PvsNP.Units.tf_fun_self_append hRev
  have heq : (fun x : List Bool => (x ++ x).reverse)
      = (List.reverse ∘ fun x : List Bool => x ++ x) := by
    funext x
    rfl
  rwa [heq]
