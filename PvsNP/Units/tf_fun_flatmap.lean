import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_inv_hom_closed

set_option autoImplicit false

/-
Doubling every bit of a binary string takes polynomial time (TM2).
The settled unit m2_inv_hom_closed already proves that flatMap of ANY
function `h : Bool → List Bool` is polytime (`cpt_flatMap`, built by iterating
its one-step transducer `ihStep`); instantiating `h := fun b => [b, b]` gives
exactly this statement. The upstream `ComputableInPolyTime (fun x => x)
(fun x => x)` is the same type as the campaign's `PolyTimeComputable
encodeString encodeString` (both are `Nonempty (TM2ComputableInPolyTime …)`
with the identity encoding), so the term is accepted directly, as in
m2_inv_hom_closed's own closing theorem.
-/

/-- Doubling every bit of a binary string takes polynomial time (TM2). -/
theorem PvsNP.Units.tf_fun_flatmap :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.flatMap fun b => [b, b]) :=
  PvsNP.Units.m2_inv_hom_closed.cpt_flatMap (fun b => [b, b])
