import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_count_binary
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_tm_count_false_binary

open Turing

/-- Counting `false`s is counting `true`s of the bitwise complement. -/
theorem count_false_eq_count_true_map_not (x : List Bool) :
    x.count false = (x.map not).count true := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [ih]

/-- The bitwise complement is polynomial-time computable: it is a `filterMap`. -/
theorem map_not_polyTime :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.map not) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.filterMap_polyTime
    PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.map not)
    (fun b => some (!b)) (fun x => by
      show x.map not = x.filterMap (fun b => some (!b))
      induction x with
      | nil => rfl
      | cons b xs ih =>
        cases b <;>
          simp only [List.map_cons, List.filterMap_cons, Bool.not_false, Bool.not_true] <;>
          rw [ih])

end PvsNP.Units.m2_tm_count_false_binary

/-- Writing the number of falses of a string in binary takes polynomial time (TM2). -/
theorem PvsNP.Units.m2_tm_count_false_binary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (x.count false)) := by
  have hnot := PvsNP.Units.m2_tm_count_false_binary.map_not_polyTime
  have hcount := PvsNP.Units.m2_tm_count_binary
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => x.map not)
    (fun x : List Bool => Nat.bits (x.count true)) hnot hcount
  have hfun : (fun x : List Bool => Nat.bits (x.count true)) ∘
      (fun x : List Bool => x.map not)
      = (fun x : List Bool => Nat.bits (x.count false)) := by
    funext x
    simp only [Function.comp_apply]
    rw [PvsNP.Units.m2_tm_count_false_binary.count_false_eq_count_true_map_not]
  rw [hfun] at hcomp
  exact hcomp
