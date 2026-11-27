import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_two_pass_polytime

namespace PvsNP.Units.tf_fun_sort

theorem keep_count (b : Bool) (x : List Bool) :
    x.filterMap (fun a => if a = b then some b else none) =
      List.replicate (x.count b) b := by
  induction x with
  | nil => rfl
  | cons a x ih => cases a <;> cases b <;> simp_all [List.replicate_succ]

end PvsNP.Units.tf_fun_sort

/-- Keep the false bits in the first pass and the true bits in the second. -/
theorem PvsNP.Units.tf_fun_sort :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.count false) false ++
        List.replicate (x.count true) true) := by
  refine PvsNP.Units.m2_two_pass_polytime.twoPass_polyTime
    PvsNP.encodeString PvsNP.encodeString _
    (fun b : Bool => if b = false then some false else none)
    (fun b : Bool => if b = true then some true else none) ?_
  intro x
  change List.replicate (x.count false) false ++ List.replicate (x.count true) true =
    x.filterMap (fun b => if b = false then some false else none) ++
      x.filterMap (fun b => if b = true then some true else none)
  rw [PvsNP.Units.tf_fun_sort.keep_count false x,
    PvsNP.Units.tf_fun_sort.keep_count true x]
