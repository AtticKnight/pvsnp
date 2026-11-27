import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ww_in_p
import PvsNP.Units.m2_conp_down_closed
import PvsNP.Units.m2_p_subset_np_conp

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_double_conp

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

private theorem encodeBool_eq :
    (Computability.encodeBool : Bool → List Bool) = fun b => [b] := rfl

private theorem unpairB_half_fst (x : List Bool) :
    (unpairB (half x ++ false :: x)).1 = x.take (x.length / 2) := by
  rw [half_eq]
  simp [unpairB, un]

private theorem unpairB_half_snd (x : List Bool) :
    (unpairB (half x ++ false :: x)).2 = x.drop (x.length / 2) := by
  rw [half_eq]
  simp [unpairB, un]

private abbrev wwDec (x : List Bool) : Bool :=
  decide ((unpairB (half x ++ false :: x)).1 = (unpairB (half x ++ false :: x)).2)

private theorem wwDec_iff (x : List Bool) :
    wwDec x = true ↔ ∃ u : List Bool, x = u ++ u := by
  simp only [wwDec, unpairB_half_fst, unpairB_half_snd, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨x.take (x.length / 2), ?_⟩
    conv_lhs => rw [← List.take_append_drop (x.length / 2) x]
    rw [h]
  · rintro ⟨u, rfl⟩
    have hlen : (u ++ u).length / 2 = u.length := by
      rw [List.length_append]
      omega
    rw [hlen, List.take_left, List.drop_left]

private theorem cpt_wwDec :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer wwDec := by
  have hCut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => half x ++ false :: x) :=
    cpt_app2 cpt_half (cpt_cons1 false cpt_id)
  have hPair : ComputableInPolyTime (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => unpairB (half x ++ false :: x)) :=
    cpt_comp hCut cpt_unpairB
  have henc : PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
    funext ⟨a, b⟩
    simp [PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair, PvsNP.encodePair,
      Computability.encodingProd, Computability.encodingList]
  have hEq : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (fun p : List Bool × List Bool => decide (p.1 = p.2)) := by
    rw [henc]
    exact PvsNP.Units.m2_eq_polytime
  exact cpt_comp (ea := fun x : List Bool => x)
    (eb := PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair)
    (ec := Computability.encodeBool)
    (f := fun x : List Bool => unpairB (half x ++ false :: x))
    (g := fun p : List Bool × List Bool => decide (p.1 = p.2))
    hPair hEq

private def doubleRed (z : List Bool) (x : List Bool) : List Bool :=
  sel (hd [wwDec x]) z (unpairB (half x ++ false :: x)).1

private theorem doubleRed_true {z x : List Bool} (h : wwDec x = true) :
    doubleRed z x = x.take (x.length / 2) := by
  simp [doubleRed, h, hd, sel, unpairB_half_fst]

private theorem doubleRed_false {z x : List Bool} (h : wwDec x = false) :
    doubleRed z x = z := by
  simp [doubleRed, h, hd, sel]

private theorem doubleRed_polyTime (z : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (doubleRed z) := by
  have hDec : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => [wwDec x]) := by
    have h := cpt_wwDec
    have hencS : (Computability.encodingList Bool).encode = (fun x : List Bool => x) := by
      funext x
      simp [Computability.encodingList]
    unfold PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer at h
    rw [hencS, encodeBool_eq] at h
    obtain ⟨c⟩ := h
    exact ⟨{ c with outputsFun := c.outputsFun }⟩
  have hHd : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => hd [wwDec x]) :=
    cpt_comp hDec cpt_hd
  have hCut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => half x ++ false :: x) :=
    cpt_app2 cpt_half (cpt_cons1 false cpt_id)
  have hPair : ComputableInPolyTime (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => unpairB (half x ++ false :: x)) :=
    cpt_comp hCut cpt_unpairB
  have hFst : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => (unpairB (half x ++ false :: x)).1) :=
    cpt_comp hPair cpt_fst
  exact cpt_sel hHd (cpt_const z) hFst

end PvsNP.Units.tc_closure_double_conp

/-- coNP is closed under string doubling: `L ∈ coNP` implies `{u ++ u | u ∈ L} ∈ coNP`. -/
theorem PvsNP.Units.tc_closure_double_conp :
    ∀ L : Language Bool, L ∈ PvsNP.coNP →
      ({x : List Bool | ∃ u ∈ L, x = u ++ u} : Language Bool) ∈ PvsNP.coNP := by
  intro L hL
  by_cases hnon : ∃ z : List Bool, z ∉ L
  · obtain ⟨z, hz⟩ := hnon
    refine PvsNP.Units.m2_conp_down_closed _ L ?_ hL
    refine ⟨PvsNP.Units.tc_closure_double_conp.doubleRed z,
      PvsNP.Units.tc_closure_double_conp.doubleRed_polyTime z, fun x => ?_⟩
    cases hdec : PvsNP.Units.tc_closure_double_conp.wwDec x with
    | false =>
      rw [PvsNP.Units.tc_closure_double_conp.doubleRed_false hdec]
      constructor
      · rintro ⟨u, _, rfl⟩
        have ht : PvsNP.Units.tc_closure_double_conp.wwDec (u ++ u) = true :=
          (PvsNP.Units.tc_closure_double_conp.wwDec_iff (u ++ u)).mpr ⟨u, rfl⟩
        rw [ht] at hdec
        cases hdec
      · intro hmem
        exact absurd hmem hz
    | true =>
      rw [PvsNP.Units.tc_closure_double_conp.doubleRed_true hdec]
      obtain ⟨u, hu⟩ := (PvsNP.Units.tc_closure_double_conp.wwDec_iff x).mp hdec
      have htake : x.take (x.length / 2) = u := by
        subst hu
        have hlen : (u ++ u).length / 2 = u.length := by
          rw [List.length_append]
          omega
        rw [hlen, List.take_left]
      rw [htake]
      constructor
      · rintro ⟨u', hu', hxu'⟩
        have hlen1 : u.length = u'.length := by
          have := congrArg List.length (hu.symm.trans hxu')
          simp only [List.length_append] at this
          omega
        have heq : u = u' := by
          have := congrArg (List.take u.length) (hu.symm.trans hxu')
          simpa [List.take_left, hlen1] using this
        rwa [heq]
      · intro huL
        exact ⟨u, huL, hu⟩
  · have hall : ∀ z : List Bool, z ∈ L := by
      intro z
      by_contra hnz
      exact hnon ⟨z, hnz⟩
    have heq : ({x : List Bool | ∃ u ∈ L, x = u ++ u} : Language Bool) =
        {x : List Bool | ∃ y : List Bool, x = y ++ y} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun ⟨u, _, hx⟩ => ⟨u, hx⟩, fun ⟨y, hx⟩ => ⟨y, hall y, hx⟩⟩
    rw [heq]
    exact (PvsNP.Units.m2_p_subset_np_conp PvsNP.Units.m2_ww_in_p).2
