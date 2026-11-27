import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_prefix_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_const_polytime

/-- Every language of the strings with a fixed prefix is in P (TM2): fix `w`, pair it with the
input (constant + identity, `m2_const_polytime` / `cpt_id` / `cpt_pair`), then decide the prefix
relation in polynomial time (`m2_prefix_polytime`) and compose (`m2_polytime_comp`). This is the
`∀ w` generalisation of the settled unit `tl_lang_prefix_p` (fixed prefix `[true, true]`). -/
theorem PvsNP.Units.tl_lang_prefix_all_p :
    ∀ w : List Bool, ({x : List Bool | w <+: x} : Language Bool) ∈ PvsNP.P := by
  intro w
  refine ⟨fun x : List Bool => w.isPrefixOf x, ?_, fun x => ?_⟩
  · have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
        (fun x : List Bool => (w, x)) :=
      PvsNP.Units.m2_pair_build_polytime.cpt_pair
        (PvsNP.Units.m2_const_polytime w)
        PvsNP.Units.m2_pair_build_polytime.cpt_id
    exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeAnswer (fun x : List Bool => (w, x))
      (fun p : List Bool × List Bool => p.1.isPrefixOf p.2)
      hpair PvsNP.Units.m2_prefix_polytime
  · exact List.isPrefixOf_iff_prefix.symm
