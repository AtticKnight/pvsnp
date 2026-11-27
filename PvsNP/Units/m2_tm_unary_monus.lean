import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_unary_monus

theorem cpt_allTrue :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate x.length true) :=
  PvsNP.Units.m2_transducer_polytime Unit
    (fun _ _ => ((), some true))
    (fun _ => none)
    (fun _ x => List.replicate x.length true)
    (fun _ => rfl)
    (fun _ _ _ => rfl)
    ()

end PvsNP.Units.m2_tm_unary_monus

theorem PvsNP.Units.m2_tm_unary_monus :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.replicate (p.1.length - p.2.length) true) := by
  have h1 := PvsNP.Units.m2_polytime_comp _ _ _ _ _
    PvsNP.Units.m2_tm_pair_swap_polytime PvsNP.Units.m2_take_drop_length_polytime.2
  have h2 := PvsNP.Units.m2_polytime_comp _ _ _ _ _
    h1 PvsNP.Units.m2_tm_unary_monus.cpt_allTrue
  convert h2 using 1
  funext p
  simp only [Function.comp, List.length_drop]
