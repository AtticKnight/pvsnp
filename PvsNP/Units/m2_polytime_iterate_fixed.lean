import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.m2_polytime_iterate_fixed

/-- Iterating `g` a fixed number of times stays polynomial-time: induction on the
number of iterations. The zero case is the identity, written as reverse twice
(the settled unit `m2_reverse_polytime`); each successor case composes with `g`
(the settled unit `m2_polytime_comp`, `Function.iterate_succ'`). -/
theorem main (g : List Bool → List Bool) (m : ℕ)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => g^[m] x) := by
  induction m with
  | zero =>
    have hid : (fun x : List Bool => x.reverse) ∘ (fun x : List Bool => x.reverse)
        = (fun x : List Bool => x) := by
      funext x
      simp [Function.comp_apply, List.reverse_reverse]
    have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
      PvsNP.encodeString (fun x : List Bool => x.reverse) (fun x : List Bool => x.reverse)
      PvsNP.Units.m2_reverse_polytime PvsNP.Units.m2_reverse_polytime
    rw [hid] at hcomp
    have h0 : (fun x : List Bool => g^[0] x) = (fun x : List Bool => x) := by
      funext x
      simp [Function.iterate_zero_apply]
    rw [h0]
    exact hcomp
  | succ m ih =>
    have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
      PvsNP.encodeString g (fun y : List Bool => g^[m] y) hg ih
    have heq : (fun y : List Bool => g^[m] y) ∘ g
        = (fun x : List Bool => g^[m + 1] x) := by
      funext x
      simp [Function.comp_apply, Function.iterate_succ']
    rwa [heq] at hcomp

end PvsNP.Units.m2_polytime_iterate_fixed

theorem PvsNP.Units.m2_polytime_iterate_fixed :
    ∀ (g : List Bool → List Bool) (m : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g →
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => g^[m] x) :=
  fun g m hg => PvsNP.Units.m2_polytime_iterate_fixed.main g m hg
