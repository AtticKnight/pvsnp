import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_tm_y_pairs_combine

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

def pairδ (g : Bool → Bool → Bool) : Option Bool → Bool → Option Bool × Option Bool
  | none, a => (some a, none)
  | some a, b => (none, some (g a b))

theorem pair_run (g : Bool → Bool → Bool) :
    ∀ x : List Bool,
      (List.range (x.length / 2)).map (fun i => g (x.getD (2 * i) false) (x.getD (2 * i + 1) false)) =
        fstRun (pairδ g) (fun _ => none) none x
  | [] => rfl
  | [_] => by simp [fstRun, pairδ]
  | a :: b :: t => by
    have hlen : (a :: b :: t).length / 2 = t.length / 2 + 1 := by
      simp only [List.length_cons]
      omega
    rw [hlen, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [fstRun, pairδ, Option.toList_none, Option.toList_some, List.nil_append,
      List.singleton_append]
    congr 1
    rw [← pair_run g t]
    refine List.map_congr_left (fun j _ => ?_)
    simp only [Function.comp_apply]
    have h1 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    rw [h1]
    simp [List.getD]
termination_by x => x.length

theorem pairs_combine_aux (g : Bool → Bool → Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool =>
        (List.range (x.length / 2)).map
          (fun i => g (x.getD (2 * i) false) (x.getD (2 * i + 1) false))) :=
  fst_polyTime (fun x : List Bool => x) (fun x : List Bool => x) _
    (pairδ g) (fun _ => none) none (pair_run g)

end PvsNP.Units.m2_tm_y_pairs_combine

/-- Combining adjacent pairs of bits with a fixed binary Boolean function takes polynomial time (TM2). -/
theorem PvsNP.Units.m2_tm_y_pairs_combine :
    ∀ g : Bool → Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool =>
          (List.range (x.length / 2)).map
            (fun i => g (x.getD (2 * i) false) (x.getD (2 * i + 1) false))) :=
  PvsNP.Units.m2_tm_y_pairs_combine.pairs_combine_aux
