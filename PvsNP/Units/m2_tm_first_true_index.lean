import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_tm_first_true_index

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private def step : Bool → Bool → Bool × Option Bool
  | false, false => (false, some true)
  | _, _ => (true, none)

private theorem finished (xs : List Bool) :
    fstRun step (fun _ => none) true xs = [] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa [fstRun, step] using ih

private theorem scans (xs : List Bool) :
    fstRun step (fun _ => none) false xs =
      List.replicate (xs.takeWhile (fun b : Bool => !b)).length true := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [fstRun, step, finished, List.takeWhile, ih, List.replicate_succ]

end PvsNP.Units.m2_tm_first_true_index

open PvsNP.Units.fr_ladner.PEqualNP.Library PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
  PvsNP.Units.m2_tm_first_true_index in
/-- Emit one unary digit per leading false bit. The first true bit stops output permanently. -/
theorem PvsNP.Units.m2_tm_first_true_index :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate (x.takeWhile (fun b : Bool => !b)).length true) :=
  fst_polyTime _ _ _ step (fun _ => none) false (fun xs => (scans xs).symm)
