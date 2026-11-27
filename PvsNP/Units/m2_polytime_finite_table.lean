import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_polytime_finite_patch

/-- A finite lookup table is a finite modification of the constant default function. -/
theorem PvsNP.Units.m2_polytime_finite_table :
    ∀ (f : List Bool → List Bool) (u : List Bool) (S : Finset (List Bool)),
      (∀ x : List Bool, x ∉ S → f x = u) →
        PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f := by
  intro f u S agrees
  exact PvsNP.Units.m2_polytime_finite_patch (fun _ => u) f S
    (PvsNP.Units.m2_const_polytime u) agrees
