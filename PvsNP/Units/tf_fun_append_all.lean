import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-- Append the fixed word by feeding the input machine and a constant machine to list concatenation. -/
theorem PvsNP.Units.tf_fun_append_all :
    ∀ w : List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x ++ w) := by
  intro w
  have h := cpt_app2 cpt_id (cpt_const w)
  exact h
