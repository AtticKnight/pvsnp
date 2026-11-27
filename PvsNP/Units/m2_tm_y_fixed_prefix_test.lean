import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_prefix_polytime
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.m2_tm_y_fixed_prefix_test

end PvsNP.Units.m2_tm_y_fixed_prefix_test

/-- Testing whether a string starts with a fixed string takes polynomial time (TM2).

For a fixed `w`, the map `x ↦ (w, x)` is polynomial-time computable: the constant
function `fun _ => w` is (settled unit `m2_const_polytime`), the identity is
(Mathlib's `Turing.idComputableInPolyTime`), and the two are paired by the settled
unit `m2_pair_build_polytime`. Composing that pair-builder with the settled
`m2_prefix_polytime` decider via the settled unit `m2_polytime_comp` gives the
decider `x ↦ w.isPrefixOf x`. -/
theorem PvsNP.Units.m2_tm_y_fixed_prefix_test :
    ∀ w : List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => w.isPrefixOf x) := by
  intro w
  have hconst : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun _ : List Bool => w) :=
    PvsNP.Units.m2_const_polytime w
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString id :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (w, x)) :=
    PvsNP.Units.m2_pair_build_polytime (fun _ : List Bool => w) id hconst hid
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
    PvsNP.encodeAnswer (fun x : List Bool => (w, x))
    (fun p : List Bool × List Bool => p.1.isPrefixOf p.2) hpair
    PvsNP.Units.m2_prefix_polytime
