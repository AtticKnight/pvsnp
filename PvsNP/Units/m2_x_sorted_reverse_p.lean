import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.tl_lang_sorted_p

/-
Built on the settled units PvsNP.Units.fr_ladner, PvsNP.Units.m2_reverse_polytime and PvsNP.Units.tl_lang_sorted_p of github.com/makedotfun/pvsnp (Apache License 2.0), which this
file imports.
-/

/-- The strings whose reversal is sorted are in P (TM2): reverse, then decide sortedness. -/
theorem PvsNP.Units.m2_x_sorted_reverse_p :
    ({x : List Bool | List.SortedLE x.reverse} : Language Bool) ∈ PvsNP.P := by
  obtain ⟨d, hd, hdec⟩ := PvsNP.Units.tl_lang_sorted_p
  exact ⟨fun x => d x.reverse, PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp PvsNP.Units.m2_reverse_polytime hd,
    fun x => hdec x.reverse⟩
