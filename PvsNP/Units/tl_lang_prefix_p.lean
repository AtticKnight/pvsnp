import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_prefix_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_const_polytime

theorem PvsNP.Units.tl_lang_prefix_p :
    ({x : List Bool | [true, true] <+: x} : Language Bool) ∈ PvsNP.P := by
  refine ⟨fun x : List Bool => [true, true].isPrefixOf x, ?_, fun x => ?_⟩
  · have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
        (fun x : List Bool => ([true, true], x)) :=
      PvsNP.Units.m2_pair_build_polytime.cpt_pair
        (PvsNP.Units.m2_const_polytime [true, true])
        PvsNP.Units.m2_pair_build_polytime.cpt_id
    exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeAnswer (fun x : List Bool => ([true, true], x))
      (fun p : List Bool × List Bool => p.1.isPrefixOf p.2)
      hpair PvsNP.Units.m2_prefix_polytime
  · exact List.isPrefixOf_iff_prefix.symm
