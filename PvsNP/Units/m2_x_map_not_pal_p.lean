import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_palindrome_in_p

/-
Built on the settled units PvsNP.Units.fr_ladner and PvsNP.Units.m2_palindrome_in_p of github.com/makedotfun/pvsnp (Apache License 2.0), which this
file imports.
-/

namespace PvsNP.Units.m2_x_map_not_pal_p

theorem mapnot_eq (a : List Bool) : a.map not = a.filterMap (fun b : Bool => some (!b)) := by
  induction a with
  | nil => rfl
  | cons b a ih =>
    rw [List.map_cons, ih]
    rfl

theorem cpt_mapnot : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x.map not) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.filterMap_polyTime (fun x : List Bool => x) (fun x : List Bool => x) _
    (fun b : Bool => some (!b)) mapnot_eq

end PvsNP.Units.m2_x_map_not_pal_p

/-- The strings whose complement is a palindrome are in P (TM2): complement each bit, then decide
palindromes. -/
theorem PvsNP.Units.m2_x_map_not_pal_p :
    ({x : List Bool | (x.map not).reverse = x.map not} : Language Bool) ∈ PvsNP.P := by
  obtain ⟨d, hd, hdec⟩ := PvsNP.Units.m2_palindrome_in_p
  exact ⟨fun x => d (x.map not), PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp PvsNP.Units.m2_x_map_not_pal_p.cpt_mapnot hd,
    fun x => hdec (x.map not)⟩
