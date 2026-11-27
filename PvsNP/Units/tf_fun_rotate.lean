import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_rotate_closed

/-- Rotating a binary string left by 1 takes polynomial time (TM2). -/
theorem PvsNP.Units.tf_fun_rotate :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.rotate 1) :=
  PvsNP.Units.m2_p_rotate_closed.cpt_rotate
