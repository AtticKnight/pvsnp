import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Putting [true, false] in front of a binary string takes polynomial time: write the
two fixed bits, then copy the input. Both pieces are polytime machines from the
settled unit PvsNP.Units.fr_ladner, combined by cpt_app2.
-/

namespace PvsNP.Units.tf_fun_prepend

end PvsNP.Units.tf_fun_prepend

/-- Putting [true, false] in front of a binary string takes polynomial time (TM2). -/
theorem PvsNP.Units.tf_fun_prepend :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => [true, false] ++ x) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const [true, false])
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
