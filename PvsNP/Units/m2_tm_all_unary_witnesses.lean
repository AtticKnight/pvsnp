import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.m2_bool_combine_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_all_unary_witnesses

theorem main : ∀ V : List Bool × List Bool → Bool,
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V →
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
        (fun x : List Bool => (List.range (x.length + 1)).all (fun i => V (x, List.replicate i true))) := by
  intro V hV
  have hN := PvsNP.Units.m2_tm_pair_bool_combine (fun a _ => !a) V V hV hV
  have hS := PvsNP.Units.m2_bounded_unary_search_polytime _ hN
  have hA := PvsNP.Units.m2_bool_combine_polytime (fun a _ => !a) _ _ hS hS
  convert hA using 1
  funext x
  simp [List.all_eq_not_any_not]

end PvsNP.Units.m2_tm_all_unary_witnesses

theorem PvsNP.Units.m2_tm_all_unary_witnesses :
    ∀ V : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V →
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
        (fun x : List Bool => (List.range (x.length + 1)).all (fun i => V (x, List.replicate i true))) :=
  PvsNP.Units.m2_tm_all_unary_witnesses.main
