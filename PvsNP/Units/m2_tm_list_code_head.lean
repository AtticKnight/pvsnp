import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_tm_list_code_head

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private def wire (l : List (List Bool)) : List Bool :=
  (l.map (fun w => w.flatMap (fun b => [b, b]) ++ [false, true])).flatten

private theorem wire_cons (w : List Bool) (ws : List (List Bool)) :
    wire (w :: ws) = w.flatMap (fun b => [b, b]) ++ false :: true :: wire ws := by
  simp [wire, List.append_assoc]

private def step : Option (Option Bool) → Bool → Option (Option Bool) × Option Bool
  | none, _ => (none, none)
  | some none, b => (some (some b), none)
  | some (some a), b => if a == b then (some none, some a) else (none, none)

private theorem dataWord (w tail : List Bool) :
    fstRun step (fun _ => none) (some none) (w.flatMap (fun b => [b, b]) ++ tail) =
      w ++ fstRun step (fun _ => none) (some none) tail := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [fstRun, step, ih]

private theorem stopped (xs : List Bool) :
    fstRun step (fun _ => none) none xs = [] := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simpa [fstRun, step] using ih

private theorem reads (l : List (List Bool)) :
    fstRun step (fun _ => none) (some none) (wire l) = l.headD [] := by
  cases l with
  | nil => rfl
  | cons w ws =>
    rw [wire_cons, dataWord]
    change w ++ fstRun step (fun _ => none) none (wire ws) = w
    rw [stopped, List.append_nil]

end PvsNP.Units.m2_tm_list_code_head

open PvsNP.Units.fr_ladner.PEqualNP.Library PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
  PvsNP.Units.m2_tm_list_code_head in
/-- The first unequal pair ends the first word; the input may end before there is a word. -/
theorem PvsNP.Units.m2_tm_list_code_head :
    PvsNP.PolyTimeComputable
      (fun l : List (List Bool) =>
        (l.map (fun w : List Bool => w.flatMap (fun b : Bool => [b, b]) ++ [false, true])).flatten)
      PvsNP.encodeString (fun l : List (List Bool) => l.headD []) :=
  fst_polyTime _ _ _ step (fun _ => none) (some none) (fun l => (reads l).symm)
