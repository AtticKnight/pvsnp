import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_unary_triangle
import PvsNP.Units.m2_unary_to_binary_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

/-- The triangular number of a length, in binary, takes polynomial time (TM2).

Compute the triangular number in unary (the settled unit
`m2_tm_unary_triangle`), then convert the unary count to its binary
representation (the settled unit `m2_unary_to_binary_polytime`), composed by
the settled unit `m2_polytime_comp`. -/
theorem PvsNP.Units.m2_tm_y_binary_triangle_length :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (x.length * (x.length + 1) / 2)) := by
  have hTri := PvsNP.Units.m2_tm_unary_triangle
  have hBits := PvsNP.Units.m2_unary_to_binary_polytime
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString
    (fun x : List Bool => List.replicate (x.length * (x.length + 1) / 2) true)
    (fun x : List Bool => Nat.bits x.length)
    hTri hBits
  have hfun : (fun x : List Bool => Nat.bits x.length) ∘
      (fun x : List Bool => List.replicate (x.length * (x.length + 1) / 2) true) =
      (fun x : List Bool => Nat.bits (x.length * (x.length + 1) / 2)) := by
    funext x
    simp [Function.comp_apply]
  rw [hfun] at hcomp
  exact hcomp
