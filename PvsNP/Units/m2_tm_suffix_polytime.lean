import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_prefix_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.m2_tm_suffix_polytime

/-- `isSuffixOf` is `isPrefixOf` on the reversed strings, as a function equality. -/
theorem suffix_eq_rev :
    (fun p : List Bool × List Bool => p.1.isSuffixOf p.2) =
      (fun p : List Bool × List Bool => p.1.isPrefixOf p.2) ∘
        (fun p : List Bool × List Bool => (p.1.reverse, p.2.reverse)) := by
  funext ⟨x, y⟩
  simp only [Function.comp_apply, List.isSuffixOf]

end PvsNP.Units.m2_tm_suffix_polytime

/-- Testing whether one string ends another takes polynomial time: reverse both strings,
then test the start, composed by `m2_polytime_comp`. -/
theorem PvsNP.Units.m2_tm_suffix_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (fun p : List Bool × List Bool => p.1.isSuffixOf p.2) := by
  have hrev : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1.reverse, p.2.reverse)) :=
    PvsNP.Units.m2_prod_map_polytime (fun x : List Bool => x.reverse)
      (fun x : List Bool => x.reverse) PvsNP.Units.m2_reverse_polytime
      PvsNP.Units.m2_reverse_polytime
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair
    PvsNP.encodeAnswer _ _ hrev PvsNP.Units.m2_prefix_polytime
  rw [PvsNP.Units.m2_tm_suffix_polytime.suffix_eq_rev]
  exact hcomp
