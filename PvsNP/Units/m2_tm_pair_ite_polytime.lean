import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_polytime_comp

/-
Uses the settled units PvsNP/Units/fr_ladner.lean (the self-delimiting pairing `pairB` / `unpairB`
and their machines `cpt_pairB`, `cpt_unpairB`), PvsNP/Units/m2_ite_polytime.lean and
PvsNP/Units/m2_polytime_comp.lean of github.com/makedotfun/pvsnp. Nothing is copied; the units
are imported.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_pair_ite_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem pairB_poly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => pairB p.1 p.2) := cpt_pairB

theorem unpairB_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
    unpairB := cpt_unpairB

theorem main (c : List Bool × List Bool → Bool) (a b : List Bool × List Bool → List Bool)
    (hc : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer c)
    (ha : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString a)
    (hb : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString b) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => if c p = true then a p else b p) := by
  have hc' := PvsNP.Units.m2_polytime_comp _ _ _ _ _ unpairB_poly hc
  have ha' := PvsNP.Units.m2_polytime_comp _ _ _ _ _ unpairB_poly ha
  have hb' := PvsNP.Units.m2_polytime_comp _ _ _ _ _ unpairB_poly hb
  have hi := PvsNP.Units.m2_ite_polytime _ _ _ hc' ha' hb'
  have h := PvsNP.Units.m2_polytime_comp _ _ _ _ _ pairB_poly hi
  have e : (fun p : List Bool × List Bool => if c p = true then a p else b p) =
      ((fun x : List Bool => if (c ∘ unpairB) x = true then (a ∘ unpairB) x else (b ∘ unpairB) x)
        ∘ (fun p : List Bool × List Bool => pairB p.1 p.2)) := by
    funext p
    simp [Function.comp, unpairB_pairB]
  rw [e]
  exact h

end PvsNP.Units.m2_tm_pair_ite_polytime

theorem PvsNP.Units.m2_tm_pair_ite_polytime :
    ∀ (c : List Bool × List Bool → Bool) (a b : List Bool × List Bool → List Bool),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer c →
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString a →
          PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString b →
            PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
              (fun p : List Bool × List Bool => if c p = true then a p else b p) :=
  PvsNP.Units.m2_tm_pair_ite_polytime.main
