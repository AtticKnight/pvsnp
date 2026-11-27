import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Uses the settled unit PvsNP/Units/fr_ladner.lean of github.com/makedotfun/pvsnp (Apache License
2.0, adapted from github.com/brilliant-hq/pequalnp-proofs, Apache License 2.0): the flag-string
combinator `cpt_bitFlag` and the selector `cpt_sel`. Nothing is copied; the unit is imported.
-/

namespace PvsNP.Units.m2_ite_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem ite_poly (c : List Bool → Bool) (a b : List Bool → List Bool)
    (hc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer c)
    (ha : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString a)
    (hb : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString b) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => if c x = true then a x else b x) := by
  have h := cpt_sel (f := fun x => if c x = true then [true] else []) (a := b) (b := a)
    (cpt_bitFlag hc) hb ha
  have e : (fun x : List Bool => if c x = true then a x else b x) =
      fun x => sel (if c x = true then [true] else []) (b x) (a x) := by
    funext x
    by_cases hx : c x = true <;> simp [sel, hx]
  rw [e]
  exact h

end PvsNP.Units.m2_ite_polytime

/-- If-then-else of polynomial-time functions is polynomial-time. -/
theorem PvsNP.Units.m2_ite_polytime : ∀ (c : List Bool → Bool) (a b : List Bool → List Bool),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer c →
        PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString a →
          PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString b →
            PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
              (fun x : List Bool => if c x = true then a x else b x) :=
  PvsNP.Units.m2_ite_polytime.ite_poly
