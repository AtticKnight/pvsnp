import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_tm_list_code_flatten

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private def wire (l : List (List Bool)) : List Bool :=
  (l.map (fun w => w.flatMap (fun b => [b, b]) ++ [false, true])).flatten

private theorem wire_cons (w : List Bool) (ws : List (List Bool)) :
    wire (w :: ws) = w.flatMap (fun b => [b, b]) ++ false :: true :: wire ws := by
  simp [wire, List.append_assoc]

private def step : Option Bool → Bool → Option Bool × Option Bool
  | none, b => (some b, none)
  | some a, b => (none, if a == b then some a else none)

private theorem dataWord (w tail : List Bool) :
    fstRun step (fun _ => none) none (w.flatMap (fun b => [b, b]) ++ tail) =
      w ++ fstRun step (fun _ => none) none tail := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [fstRun, step, ih]

private theorem reads (l : List (List Bool)) :
    fstRun step (fun _ => none) none (wire l) = l.flatten := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
    rw [wire_cons, dataWord]
    change w ++ fstRun step (fun _ => none) none (wire ws) = w ++ ws.flatten
    rw [ih]

end PvsNP.Units.m2_tm_list_code_flatten

open PvsNP.Units.fr_ladner.PEqualNP.Library PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
  PvsNP.Units.m2_tm_list_code_flatten in
/-- Pair alignment lets a single finite-state scan omit the separators and emit each data bit once. -/
theorem PvsNP.Units.m2_tm_list_code_flatten :
    PvsNP.PolyTimeComputable
      (fun l : List (List Bool) =>
        (l.map (fun w : List Bool => w.flatMap (fun b : Bool => [b, b]) ++ [false, true])).flatten)
      PvsNP.encodeString (fun l : List (List Bool) => l.flatten) :=
  fst_polyTime _ _ _ step (fun _ => none) none (fun l => (reads l).symm)
