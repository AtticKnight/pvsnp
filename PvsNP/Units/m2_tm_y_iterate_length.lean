import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines (cpt_id)
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal (cpt_iterGrow)

/-- Use the input itself as both the unary loop clock and the initial state. -/
theorem PvsNP.Units.m2_tm_y_iterate_length :
    ∀ (g : List Bool → List Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g →
      (∀ y : List Bool, (g y).length ≤ y.length + k) →
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => g^[x.length] x) := by
  intro g k machine growth
  exact cpt_iterGrow machine k growth cpt_id cpt_id
