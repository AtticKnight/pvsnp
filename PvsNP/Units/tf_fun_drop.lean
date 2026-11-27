import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

set_option autoImplicit false

/-- Dropping the first 3 bits of a binary string takes polynomial time (TM2):
    apply `cpt_tail1` from `fr_ladner` three times. -/
theorem PvsNP.Units.tf_fun_drop :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.drop 3) := by
  have h := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail1
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail1
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail1
        PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id))
  have heq : (fun x : List Bool => x.tail.tail.tail) = (fun x : List Bool => x.drop 3) := by
    funext x
    rcases x with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rwa [heq] at h
