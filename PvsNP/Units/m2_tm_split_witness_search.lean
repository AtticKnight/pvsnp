import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_bounded_unary_search_polytime
import PvsNP.Units.m2_polytime_comp

theorem PvsNP.Units.m2_tm_split_witness_search :
    ∀ V : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V →
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
        (fun x : List Bool => (List.range (x.length + 1)).any (fun i => V (x.take i, x.drop i))) := by
  intro V hV
  have htake : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.take p.2.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      PvsNP.Units.m2_tm_pair_swap_polytime PvsNP.Units.m2_take_drop_length_polytime.1
  have hdrop : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.drop p.2.length) :=
    PvsNP.Units.m2_polytime_comp _ _ _ _ _
      PvsNP.Units.m2_tm_pair_swap_polytime PvsNP.Units.m2_take_drop_length_polytime.2
  have hfork := PvsNP.Units.m2_tm_pair_fork_polytime _ _ htake hdrop
  have hV' := PvsNP.Units.m2_polytime_comp _ _ _ _ _ hfork hV
  have hs := PvsNP.Units.m2_bounded_unary_search_polytime _ hV'
  convert hs using 1
  funext x
  simp
