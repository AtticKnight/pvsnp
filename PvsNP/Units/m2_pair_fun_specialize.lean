import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_polytime_comp

/-- Fixing one argument of a polynomial-time function on pairs, or repeating it, keeps it
polynomial-time (TM2): build the pair from the identity and the constant `y` (the settled
units `cpt_id`, `cpt_pair`, `cpt_dup` and `m2_const_polytime`), then compose with `h`
(the settled unit `m2_polytime_comp`). -/
theorem PvsNP.Units.m2_pair_fun_specialize :
    ∀ (h : List Bool × List Bool → List Bool) (y : List Bool),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString h →
        PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => h (x, y)) ∧
          PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => h (y, x)) ∧
            PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => h (x, x)) := by
  intro h y hh
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x) :=
    PvsNP.Units.m2_pair_build_polytime.cpt_id
  have hconst : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun _ : List Bool => y) :=
    PvsNP.Units.m2_const_polytime y
  refine ⟨?_, ?_, ?_⟩
  · exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun x : List Bool => (x, y)) h
      (PvsNP.Units.m2_pair_build_polytime.cpt_pair hid hconst) hh
  · exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun x : List Bool => (y, x)) h
      (PvsNP.Units.m2_pair_build_polytime.cpt_pair hconst hid) hh
  · exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun x : List Bool => (x, x)) h
      PvsNP.Units.m2_pair_build_polytime.cpt_dup hh
