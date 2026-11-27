import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_tm_pair_zip_polytime
import PvsNP.Units.m2_pair_build_polytime

namespace PvsNP.Units.tf_fun_zip_with

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

def step (saved : Option Bool) (b : Bool) : Option Bool × Option Bool :=
  match saved with
  | none => (some b, none)
  | some a => (none, some (a && b))

def readPairs (s : List Bool) : List Bool :=
  fstRun step (fun _ => none) none s

theorem decode (a b : List Bool) :
    readPairs ((List.zipWith (fun u v : Bool => [u, v]) a b).flatten) =
      List.zipWith (fun u v => u && v) a b := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons u us ih =>
    cases b with
    | nil => rfl
    | cons v vs =>
      change (u && v) :: readPairs ((List.zipWith (fun p q : Bool => [p, q]) us vs).flatten) =
        (u && v) :: List.zipWith (fun p q => p && q) us vs
      rw [ih]

end PvsNP.Units.tf_fun_zip_with

/-- Flatten the zipped pairs and consume their bits two at a time with a three-state transducer. -/
theorem PvsNP.Units.tf_fun_zip_with :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.zipWith (fun a b => a && b) p.1 p.2) := by
  have hp : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      PvsNP.Units.tf_fun_zip_with.readPairs :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fst_polyTime _ _ _
      PvsNP.Units.tf_fun_zip_with.step (fun _ => none) none (fun _ => rfl)
  have h := PvsNP.Units.m2_pair_build_polytime.cpt_comp PvsNP.Units.m2_tm_pair_zip_polytime hp
  have eqn : (fun p : List Bool × List Bool =>
      PvsNP.Units.tf_fun_zip_with.readPairs ((List.zipWith (fun a b : Bool => [a, b]) p.1 p.2).flatten)) =
      (fun p : List Bool × List Bool => List.zipWith (fun a b => a && b) p.1 p.2) :=
    funext fun p => PvsNP.Units.tf_fun_zip_with.decode p.1 p.2
  rwa [eqn] at h
