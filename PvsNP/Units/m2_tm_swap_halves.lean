import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_tm_unary_div_const

/-
Swapping the two halves of a string is polynomial-time: with n = ⌊|x|/2⌋,
build the pair (1^n, x), take its two halves by the settled units
m2_take_drop_length_polytime, pair the second half with the first, and join
them by the third conjunct of m2_pair_split_polytime, composing everything
with m2_polytime_comp.
-/

namespace PvsNP.Units.m2_tm_swap_halves

theorem main : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x.drop (x.length / 2) ++ x.take (x.length / 2)) := by
  have hdiv : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.length / 2) true) :=
    PvsNP.Units.m2_tm_unary_div_const 2
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x) :=
    PvsNP.Units.m2_pair_build_polytime.cpt_id
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (List.replicate (x.length / 2) true, x)) :=
    PvsNP.Units.m2_pair_build_polytime _ _ hdiv hid
  have hdrop : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.drop (x.length / 2)) := by
    have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString _ _ hpair PvsNP.Units.m2_take_drop_length_polytime.2
    have heq : ((fun p : List Bool × List Bool => p.2.drop p.1.length) ∘
        (fun x : List Bool => (List.replicate (x.length / 2) true, x))) =
        (fun x : List Bool => x.drop (x.length / 2)) := by
      funext x
      simp
    rwa [heq] at h
  have htake : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.take (x.length / 2)) := by
    have h := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
      PvsNP.encodeString _ _ hpair PvsNP.Units.m2_take_drop_length_polytime.1
    have heq : ((fun p : List Bool × List Bool => p.2.take p.1.length) ∘
        (fun x : List Bool => (List.replicate (x.length / 2) true, x))) =
        (fun x : List Bool => x.take (x.length / 2)) := by
      funext x
      simp
    rwa [heq] at h
  have hhalves : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (x.drop (x.length / 2), x.take (x.length / 2))) :=
    PvsNP.Units.m2_pair_build_polytime _ _ hdrop htake
  have happ : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1 ++ p.2) :=
    PvsNP.Units.m2_pair_split_polytime.2.2
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair
    PvsNP.encodeString _ _ hhalves happ
  have heq : ((fun p : List Bool × List Bool => p.1 ++ p.2) ∘
      (fun x : List Bool => (x.drop (x.length / 2), x.take (x.length / 2)))) =
      (fun x : List Bool => x.drop (x.length / 2) ++ x.take (x.length / 2)) := by
    funext x
    rfl
  rwa [heq] at hcomp

end PvsNP.Units.m2_tm_swap_halves

theorem PvsNP.Units.m2_tm_swap_halves :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.drop (x.length / 2) ++ x.take (x.length / 2)) :=
  PvsNP.Units.m2_tm_swap_halves.main
