import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-- Writing a binary string twice takes polynomial time (TM2). -/
theorem PvsNP.Units.tf_fun_self_append :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x ++ x) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
