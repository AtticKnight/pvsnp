import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_polytime_comp

/-
Built on the settled units PvsNP.Units.fr_ladner (`cpt_pair`, `cpt_id`, `cpt_const`),
m2_ite_polytime, m2_const_polytime, m2_eq_polytime, and m2_polytime_comp of
github.com/makedotfun/pvsnp (Apache License 2.0).
-/

namespace PvsNP.Units.m2_polytime_finite_patch

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

private theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

private theorem eq_const_poly (a : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => decide (x = a)) := by
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (x, a)) := by
    rw [← encodePair_eq]
    exact cpt_pair cpt_id (cpt_const a)
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
    (fun x => (x, a)) (fun p => decide (p.1 = p.2)) hpair PvsNP.Units.m2_eq_polytime

theorem main :
    ∀ (f g : List Bool → List Bool) (S : Finset (List Bool)),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f →
        (∀ x : List Bool, x ∉ S → g x = f x) →
          PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g := by
  intro f g S hf
  classical
  induction S using Finset.induction_on generalizing g with
  | empty =>
    intro hfg
    have heq : g = f := funext fun x => hfg x (Finset.notMem_empty x)
    rwa [heq]
  | insert a S' ha ih =>
    intro hfg
    let g' : List Bool → List Bool := fun x => if x = a then f a else g x
    have hg' : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g' := by
      apply ih g'
      intro x hx
      by_cases hxa : x = a
      · subst hxa; simp [g']
      · simp only [g', hxa, ↓reduceIte]
        exact hfg x (by simp [hx, hxa])
    have hite := PvsNP.Units.m2_ite_polytime
      (fun x : List Bool => decide (x = a))
      (fun _ : List Bool => g a) g'
      (eq_const_poly a) (PvsNP.Units.m2_const_polytime (g a)) hg'
    have heq : (fun x : List Bool => if decide (x = a) = true then g a else g' x) = g := by
      funext x
      by_cases hxa : x = a
      · subst hxa; simp
      · simp [g', hxa]
    rwa [heq] at hite

end PvsNP.Units.m2_polytime_finite_patch

theorem PvsNP.Units.m2_polytime_finite_patch :
    ∀ (f g : List Bool → List Bool) (S : Finset (List Bool)),
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f →
        (∀ x : List Bool, x ∉ S → g x = f x) →
          PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g :=
  PvsNP.Units.m2_polytime_finite_patch.main
