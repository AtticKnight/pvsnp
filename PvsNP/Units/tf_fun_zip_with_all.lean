import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_pair_zip_polytime
import PvsNP.Units.m2_transducer_polytime

namespace PvsNP.Units.tf_fun_zip_with_all

/-- The state holds the first input of an incomplete pair. -/
private def step (g : Bool → Bool → Bool) : Option Bool → Bool → Option Bool × Option Bool
  | none, b => (some b, none)
  | some a, b => (none, some (g a b))

private def scan (g : Bool → Bool → Bool) : Option Bool → List Bool → List Bool
  | _, [] => []
  | none, b :: rest => scan g (some b) rest
  | some a, b :: rest => g a b :: scan g none rest

private theorem paired (g : Bool → Bool → Bool) (x y : List Bool) :
    scan g none ((List.zipWith (fun a b => [a, b]) x y).flatten) = List.zipWith g x y := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a xs ih =>
    cases y with
    | nil => rfl
    | cons b ys =>
      exact congrArg (List.cons (g a b)) (ih ys)

end PvsNP.Units.tf_fun_zip_with_all

/-- Interleave the two words and evaluate each pair with a three-state machine. -/
theorem PvsNP.Units.tf_fun_zip_with_all (g : Bool → Bool → Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.zipWith g p.1 p.2) := by
  have hscan := PvsNP.Units.m2_transducer_polytime (Option Bool)
    (tf_fun_zip_with_all.step g) (fun _ => none) (tf_fun_zip_with_all.scan g)
    (by intro q; rfl) (by intro q b xs; cases q <;> rfl) none
  have machine := PvsNP.Units.m2_polytime_comp _ _ _ _ _
    PvsNP.Units.m2_tm_pair_zip_polytime hscan
  have same : ((tf_fun_zip_with_all.scan g none) ∘ (fun p : List Bool × List Bool =>
      (List.zipWith (fun a b : Bool => [a,b]) p.1 p.2).flatten)) =
      (fun p : List Bool × List Bool => List.zipWith g p.1 p.2) := by
    funext p
    exact tf_fun_zip_with_all.paired g p.1 p.2
  rwa [same] at machine
