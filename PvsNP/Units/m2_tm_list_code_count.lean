import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled campaign unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp
(Apache License 2.0), which carries the upstream PEqualNP library from
github.com/open-goat/pequalnp-proofs at commit 8df87a862bd9a618faecf10ba65bff72706442c9
(Apache License 2.0). Nothing from that unit is copied; it is imported directly.
The pair-scanning separator counter transducer and correctness proof below are original
work for unit m2_tm_list_code_count.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_list_code_count

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private def countD : Option Bool → Bool → Option Bool × Option Bool
  | none, b => (some b, none)
  | some false, true => (none, some true)
  | some _, _ => (none, none)

private theorem countD_doubled (w rest : List Bool) :
    fstRun countD (fun _ => none) none (w.flatMap (fun b : Bool => [b, b]) ++ rest) =
      fstRun countD (fun _ => none) none rest := by
  induction w with
  | nil => rfl
  | cons b ws ih =>
    cases b <;> simpa [fstRun, countD] using ih

private theorem countD_enc (l : List (List Bool)) :
    fstRun countD (fun _ => none) none
      ((l.map (fun w : List Bool => w.flatMap (fun b : Bool => [b, b]) ++ [false, true])).flatten) =
      List.replicate l.length true := by
  induction l with
  | nil => rfl
  | cons w ls ih =>
    simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.length_cons,
      List.replicate_succ]
    rw [countD_doubled]
    simp only [List.cons_append, List.nil_append, fstRun, countD, Option.toList_none,
      Option.toList_some]
    exact congrArg (true :: ·) ih

theorem list_code_count_main :
    PvsNP.PolyTimeComputable
      (fun l : List (List Bool) =>
        (l.map (fun w : List Bool => w.flatMap (fun b : Bool => [b, b]) ++ [false, true])).flatten)
      PvsNP.encodeString
      (fun l : List (List Bool) => List.replicate l.length true) :=
  fst_polyTime _ _ _ countD (fun _ => none) none (fun l => (countD_enc l).symm)

end PvsNP.Units.m2_tm_list_code_count

theorem PvsNP.Units.m2_tm_list_code_count :
    PvsNP.PolyTimeComputable
      (fun l : List (List Bool) =>
        (l.map (fun w : List Bool => w.flatMap (fun b : Bool => [b, b]) ++ [false, true])).flatten)
      PvsNP.encodeString
      (fun l : List (List Bool) => List.replicate l.length true) :=
  PvsNP.Units.m2_tm_list_code_count.list_code_count_main
