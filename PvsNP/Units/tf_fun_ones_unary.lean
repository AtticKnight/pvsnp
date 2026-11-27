import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.tf_fun_ones_unary

/-- Keep each `true`, drop each `false`. -/
def keepTrue (b : Bool) : Option Bool := if b then some true else none

/-- Keeping the trues of `x` leaves `x.count true` copies of `true`. -/
theorem replicate_eq (x : List Bool) :
    List.replicate (x.count true) true = x.filterMap keepTrue := by
  induction x with
  | nil => rfl
  | cons b l ih =>
    cases b
    · simp [keepTrue, ih]
    · simp [keepTrue, List.replicate_succ, ih]

end PvsNP.Units.tf_fun_ones_unary

/-- Writing the number of trues in unary is one filter-map pass over the input
(`Machines.filterMap_polyTime`, settled unit `fr_ladner`). -/
theorem PvsNP.Units.tf_fun_ones_unary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.count true) true) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.filterMap_polyTime _ _ _
    PvsNP.Units.tf_fun_ones_unary.keepTrue
    (fun x => PvsNP.Units.tf_fun_ones_unary.replicate_eq x)
