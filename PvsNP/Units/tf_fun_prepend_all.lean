import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.tf_fun_prepend_all

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

/-- Prepending a fixed string is polynomial-time: it is the pointwise append of a
constant function and the identity, both polynomial-time. -/
theorem prepend_polyTime (w : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => w ++ x) :=
  cpt_app2 (cpt_const w) cpt_id

end PvsNP.Units.tf_fun_prepend_all

/-- Putting any fixed binary string in front takes polynomial time. -/
theorem PvsNP.Units.tf_fun_prepend_all :
    ∀ w : List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => w ++ x) :=
  fun w => PvsNP.Units.tf_fun_prepend_all.prepend_polyTime w
