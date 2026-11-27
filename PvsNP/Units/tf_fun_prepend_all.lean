import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-- Concatenate a constant output with the unmodified input. -/
theorem PvsNP.Units.tf_fun_prepend_all :
    ∀ w : List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => w ++ x) := by
  intro w
  have h := cpt_app2 (cpt_const w) cpt_id
  exact h
