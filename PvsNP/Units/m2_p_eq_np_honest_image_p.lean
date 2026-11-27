import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_polytime_comp

/-
Built on the settled units PvsNP.Units.fr_ladner, PvsNP.Units.m2_eq_polytime,
and PvsNP.Units.m2_polytime_comp of github.com/makedotfun/pvsnp (Apache License 2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_p_eq_np_honest_image_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := rfl

private theorem cptE' {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f g : α → β} (h : ComputableInPolyTime ea eb f) (heq : ∀ a, f a = g a) :
    ComputableInPolyTime ea eb g := by
  obtain rfl : f = g := funext heq
  exact h

theorem main :
    PvsNP.P = PvsNP.NP → ∀ (f : List Bool → List Bool) (q : Polynomial ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f →
        (∀ x : List Bool, x.length ≤ q.eval (f x).length) →
          ({y : List Bool | ∃ x : List Bool, f x = y} : Language Bool) ∈ PvsNP.P := by
  intro hPNP f q hf hq
  rw [hPNP]
  have hf' : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f := hf
  have hmap : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, f p.2)) := by
    rw [← encodePair_eq]
    refine cptE' (cpt_comp cpt_pairB (cpt_pair cpt_unpairB1 (cpt_comp cpt_unpairB2 hf'))) ?_
    rintro ⟨y, x⟩
    simp only [Function.comp_apply, unpairB_pairB]
  have hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.1 = f p.2)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => (p.1, f p.2))
      (fun p : List Bool × List Bool => decide (p.1 = p.2))
      hmap PvsNP.Units.m2_eq_polytime
  refine ⟨fun p => decide (p.1 = f p.2), q, hV, fun y => ?_⟩
  change (∃ x : List Bool, f x = y) ↔
    ∃ w : List Bool, w.length ≤ q.eval y.length ∧ decide (y = f w) = true
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, hq x, by simp⟩
  · rintro ⟨w, _, hw⟩
    exact ⟨w, (of_decide_eq_true hw).symm⟩

end PvsNP.Units.m2_p_eq_np_honest_image_p

theorem PvsNP.Units.m2_p_eq_np_honest_image_p :
    PvsNP.P = PvsNP.NP → ∀ (f : List Bool → List Bool) (q : Polynomial ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f →
        (∀ x : List Bool, x.length ≤ q.eval (f x).length) →
          ({y : List Bool | ∃ x : List Bool, f x = y} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.m2_p_eq_np_honest_image_p.main
