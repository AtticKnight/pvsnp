import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.tl_lang_sorted_p
import PvsNP.Units.tf_fun_flatmap_all

set_option autoImplicit false

/-
The bit-flipped sorted lists are in `P` (TM2).

Flipping every bit is polynomial time: `List.map not` is `List.flatMap (fun b => [not b])`
(`List.map_eq_flatMap`), and the settled unit `tf_fun_flatmap_all` proves `flatMap` of any
`h : Bool → List Bool` polytime. Hence bit-flip Karp-reduces this language to the sorted
strings (the settled unit `tl_lang_sorted_p`): `x.map not` is sorted exactly when `x` is in
this language, by definition of the two set-builder languages. `P` is closed downward under
Karp reductions (the settled unit `m2_p_down_closed`), which gives the result.

Note: the hint's `tf_fun_map_not` does not exist in the repo (no such file or theorem);
`tf_fun_flatmap_all` is the settled unit that actually proves the bit-flip polytime.
-/

namespace PvsNP.Units.m2_x_sorted_map_not_p

/-- Flipping every bit of a binary string takes polynomial time (TM2). -/
theorem mapNot_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.map not) := by
  have h := PvsNP.Units.tf_fun_flatmap_all (fun b : Bool => [not b])
  have heq : (fun x : List Bool => x.map not)
      = (fun x : List Bool => x.flatMap fun b => [not b]) := by
    funext x
    exact List.map_eq_flatMap
  rw [heq]
  exact h

/-- Bit-flip Karp-reduces the bit-flipped sorted lists to the sorted lists. -/
theorem red : PvsNP.KarpReducible
    ({x : List Bool | List.SortedLE (x.map not)} : Language Bool)
    ({x : List Bool | List.SortedLE x} : Language Bool) :=
  ⟨fun x : List Bool => x.map not,
    PvsNP.Units.m2_x_sorted_map_not_p.mapNot_polyTime, fun _ => Iff.rfl⟩

end PvsNP.Units.m2_x_sorted_map_not_p

/-- The bit-flipped sorted lists of booleans are in `P` (TM2). -/
theorem PvsNP.Units.m2_x_sorted_map_not_p :
    ({x : List Bool | List.SortedLE (x.map not)} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.m2_p_down_closed _ _
    PvsNP.Units.m2_x_sorted_map_not_p.red
    PvsNP.Units.tl_lang_sorted_p
