import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_adj_with

/-- Transition of the one-bit-memory transducer: remember the current bit,
    and once a previous bit exists, output the AND of the previous bit
    and the current one. -/
def adjδ : Option Bool → Bool → Option Bool × Option Bool
  | none, b => (some b, none)
  | some a, b => (some b, some (a && b))

/-- No final output. -/
def adjFin : Option Bool → Option Bool := fun _ => none

/-- The transducer's output function: from state `none` it is
    `List.zipWith (· && ·) x x.tail`; from `some a` it is the same
    zipWith over `a :: x` against `x`. -/
def adjF : Option Bool → List Bool → List Bool
  | none, x => List.zipWith (fun a b => a && b) x x.tail
  | some a, x => List.zipWith (fun a b => a && b) (a :: x) x

end PvsNP.Units.tf_fun_adj_with

open PvsNP.Units.tf_fun_adj_with

/-- Combining each bit of a binary string with the next by and takes
    polynomial time (TM2). -/
theorem PvsNP.Units.tf_fun_adj_with :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.zipWith (fun a b => a && b) x x.tail) := by
  have key := PvsNP.Units.m2_transducer_polytime (Option Bool) adjδ adjFin adjF
    (by intro q; cases q <;> simp [adjF, adjFin])
    (by intro q b x; cases q <;> simp [adjF, adjδ])
    none
  exact key
