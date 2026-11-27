import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_concat
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_eq_polytime

/-
Built on the settled units PvsNP.Units.m2_p_concat, PvsNP.Units.m2_const_polytime, and
PvsNP.Units.m2_eq_polytime of github.com/makedotfun/pvsnp (Apache License 2.0), where
m2_p_concat's machine combinators come from github.com/open-goat/pequalnp-proofs (formerly
brilliant-hq/pequalnp-proofs) at commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License
2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_karp_finite_patch

open PvsNP.Units.m2_p_concat.PEqualNP.Library
open PvsNP.Units.m2_p_concat.PEqualNP.Library.Machines

private theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem encodePair_eq : encodePair = PvsNP.encodePair := by
  funext ⟨x, y⟩
  simp [encodePair, PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]

private theorem cpt_ifEmpty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then p.2 else []) := by
  obtain ⟨c⟩ := PvsNP.Units.m2_const_polytime []
  have hI := Iter.iter_polyTime (fun _ : List Bool => ([] : List Bool)) c 0 (by simp)
  refine cpt_congr (cpt_comp cpt_swap hI) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp [Function.iterate_succ_apply']

private theorem cpt_ifNonempty :
    ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => if p.1 = [] then [] else p.2) := by
  have hneg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => if x = [] then [true] else []) :=
    cpt_comp (cpt_pair cpt_id (PvsNP.Units.m2_const_polytime [true])) cpt_ifEmpty
  refine cpt_congr (cpt_comp (cpt_first hneg) cpt_ifEmpty) ?_
  rintro ⟨x, w⟩
  cases x with
  | nil => simp
  | cons b l => simp

private theorem cpt_bitFlag {f : List Bool → Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun a => if f a then [true] else []) := by
  have h : ComputableInPolyTime Computability.encodeBool (fun x : List Bool => x)
      (fun b : Bool => if b then [true] else []) := by
    refine filterMap_polyTime _ _ _ (fun b : Bool => if b then some true else none) ?_
    intro b
    cases b <;> simp [Computability.encodeBool]
  exact cpt_comp hf h

private theorem ite_poly (c : List Bool → Bool) (a b : List Bool → List Bool)
    (hc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer c)
    (ha : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString a)
    (hb : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString b) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => if c x = true then a x else b x) := by
  have hflag := cpt_bitFlag hc
  have h1 := cpt_comp (cpt_pair hflag hb) cpt_ifEmpty
  have h2 := cpt_comp (cpt_pair hflag ha) cpt_ifNonempty
  refine cpt_congr (cpt_comp (cpt_pair h1 h2) cpt_append) ?_
  intro x
  cases hx : c x <;> simp

private theorem patch_poly (S : Finset (List Bool)) (g h : List Bool → List Bool)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g)
    (hagree : ∀ x : List Bool, x ∉ S → g x = h x) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString h := by
  classical
  induction S using Finset.induction_on generalizing h with
  | empty =>
    have heq : g = h := funext fun x => hagree x (Finset.notMem_empty x)
    rw [← heq]
    exact hg
  | @insert w S hw ih =>
    let h' : List Bool → List Bool := fun x => if x = w then g x else h x
    have hh' : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString h' := by
      apply ih h'
      intro x hx
      by_cases hxw : x = w
      · simp [h', hxw]
      · simp only [h', hxw, ↓reduceIte]
        exact hagree x (by simp [hx, hxw])
    have heq_p : ComputableInPolyTime encodePair Computability.encodeBool
        (fun p : List Bool × List Bool => decide (p.1 = p.2)) := by
      rw [encodePair_eq]
      exact PvsNP.Units.m2_eq_polytime
    have hcond : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
        (fun x : List Bool => decide (x = w)) :=
      cpt_comp (cpt_pair cpt_id (PvsNP.Units.m2_const_polytime w)) heq_p
    have hpatched : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => if decide (x = w) = true then h w else h' x) :=
      ite_poly _ _ _ hcond (PvsNP.Units.m2_const_polytime (h w)) hh'
    have heq : (fun x : List Bool => if decide (x = w) = true then h w else h' x) = h := by
      funext x
      by_cases hxw : x = w
      · subst hxw
        simp
      · simp [h', hxw]
    rwa [heq] at hpatched

private theorem karp_finite_patch
    (L₁ L₁' L₂ : Language Bool) (S : Finset (List Bool))
    (hred : PvsNP.KarpReducible L₁ L₂)
    (hy : ∃ y : List Bool, y ∈ L₂) (hz : ∃ z : List Bool, z ∉ L₂)
    (hagree : ∀ x : List Bool, x ∉ S → (x ∈ L₁ ↔ x ∈ L₁')) :
    PvsNP.KarpReducible L₁' L₂ := by
  classical
  obtain ⟨f, hf, hf_red⟩ := hred
  obtain ⟨y, hyL⟩ := hy
  obtain ⟨z, hzL⟩ := hz
  let h : List Bool → List Bool := fun x =>
    if x ∈ S then (if x ∈ L₁' then y else z) else f x
  refine ⟨h, patch_poly S f h hf ?_, ?_⟩
  · intro x hx
    simp [h, hx]
  · intro x
    by_cases hx : x ∈ S
    · by_cases hxL : x ∈ L₁'
      · simp [h, hx, hxL, hyL]
      · simp [h, hx, hxL, hzL]
    · simp only [h, hx, ↓reduceIte]
      exact (hagree x hx).symm.trans (hf_red x)

end PvsNP.Units.m2_karp_finite_patch

theorem PvsNP.Units.m2_karp_finite_patch :
    ∀ (L₁ L₁' L₂ : Language Bool) (S : Finset (List Bool)), PvsNP.KarpReducible L₁ L₂ →
      (∃ y : List Bool, y ∈ L₂) → (∃ z : List Bool, z ∉ L₂) →
        (∀ x : List Bool, x ∉ S → (x ∈ L₁ ↔ x ∈ L₁')) → PvsNP.KarpReducible L₁' L₂ :=
  PvsNP.Units.m2_karp_finite_patch.karp_finite_patch
