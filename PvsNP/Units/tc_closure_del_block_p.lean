import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tc_closure_rev_factor_p

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_del_block_p_aux

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.tc_closure_rev_factor_p_aux

def cand (x i_str : List Bool) : List Bool :=
  let p1 := revIter i_str x
  let u_rev := (unpairB p1).1
  let v := (unpairB p1).2
  let u := (unpairB (revIter i_str u_rev)).1
  u ++ [true, false] ++ v

theorem cpt_cand {x i_str : List Bool → List Bool} (hx : CPT x) (hi : CPT i_str) :
    CPT (fun s => cand (x s) (i_str s)) := by
  have hp1 : CPT (fun s => revIter (i_str s) (x s)) := cpt_revIter hi hx
  have hu_rev : CPT (fun s => (unpairB (revIter (i_str s) (x s))).1) := cpt_unpairB1_1 hp1
  have hv : CPT (fun s => (unpairB (revIter (i_str s) (x s))).2) := cpt_unpairB2_1 hp1
  have hu : CPT (fun s => (unpairB (revIter (i_str s) (unpairB (revIter (i_str s) (x s))).1)).1) :=
    cpt_unpairB1_1 (cpt_revIter hi hu_rev)
  exact cpt_app2 (cpt_app2 hu (cpt_const [true, false])) hv

theorem cand_eq (x i_str : List Bool) (hi : i_str.length ≤ x.length) :
    cand x i_str = x.take i_str.length ++ [true, false] ++ x.drop i_str.length := by
  have hp1 : revIter i_str x = pairB (x.take i_str.length).reverse (x.drop i_str.length) :=
    revIter_pair i_str x hi
  have hulen : i_str.length ≤ (x.take i_str.length).reverse.length := by
    rw [List.length_reverse, List.length_take_of_le hi]
  have hu_rev : revIter i_str (x.take i_str.length).reverse =
      pairB ((x.take i_str.length).reverse.take i_str.length).reverse
        ((x.take i_str.length).reverse.drop i_str.length) :=
    revIter_pair i_str _ hulen
  have htake_all : (x.take i_str.length).reverse.take i_str.length = (x.take i_str.length).reverse := by
    apply List.take_of_length_le
    rw [List.length_reverse, List.length_take_of_le hi]
  simp only [cand, hp1, unpairB_pairB, hu_rev, htake_all, List.reverse_reverse]

def checkFlag (f : List Bool → Bool) (x i_str : List Bool) : List Bool :=
  if f (cand x i_str) then [true] else []

theorem cpt_checkFlag (f : List Bool → Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f)
    {x i_str : List Bool → List Bool} (hx : CPT x) (hi : CPT i_str) :
    CPT (fun s => checkFlag f (x s) (i_str s)) := by
  have hbf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun a => if f a then [true] else []) :=
    cpt_bitFlag hf
  exact cpt_comp (cpt_cand hx hi) hbf

def outerStep (f : List Bool → Bool) (s : List Bool) : List Bool :=
  let acc := (unpairB s).1
  let ix := (unpairB s).2
  let i_str := (unpairB ix).1
  let x := (unpairB ix).2
  let bit := checkFlag f x i_str
  let acc' := sel acc bit [true]
  pairB acc' (pairB (true :: i_str) x)

theorem cpt_outerStep (f : List Bool → Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f) :
    CPT (outerStep f) := by
  have hacc : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hix : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hi : CPT (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hix
  have hx : CPT (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hix
  have hbit := cpt_checkFlag f hf hx hi
  have hacc' := cpt_sel hacc hbit (cpt_const [true])
  exact cpt_pairB2 hacc' (cpt_pairB2 (cpt_cons1 true hi) hx)

theorem outerStep_len (f : List Bool → Bool) (s : List Bool) :
    (outerStep f s).length ≤ s.length + 6 := by
  have h1 := unpairB_len s
  have h2 := unpairB_len (unpairB s).2
  have hacc : (sel (unpairB s).1
      (checkFlag f (unpairB (unpairB s).2).2 (unpairB (unpairB s).2).1)
      [true]).length ≤ 1 := by
    simpa [checkFlag] using sel_bit_len (unpairB s).1 _
  simp only [outerStep, pairB, un, List.length_append, List.length_cons,
    List.length_replicate]
  omega

theorem outerStep_iter_spec (f : List Bool → Bool) (m : ℕ) (acc i_str x : List Bool) :
    ∃ acc',
      (outerStep f)^[m] (pairB acc (pairB i_str x)) =
        pairB acc' (pairB (List.replicate m true ++ i_str) x) ∧
      (acc' ≠ [] ↔ acc ≠ [] ∨ ∃ j < m, checkFlag f x (List.replicate j true ++ i_str) ≠ []) := by
  induction m generalizing acc i_str with
  | zero =>
    refine ⟨acc, by simp, by simp⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hstep : outerStep f (pairB acc (pairB i_str x)) =
        pairB (sel acc (checkFlag f x i_str) [true]) (pairB (true :: i_str) x) := by
      simp [outerStep, unpairB_pairB]
    rw [hstep]
    obtain ⟨acc', h1, h2⟩ := ih (sel acc (checkFlag f x i_str) [true]) (true :: i_str)
    refine ⟨acc', ?_, ?_⟩
    · simpa [List.replicate_succ', List.append_assoc] using h1
    · rw [h2, sel_ne_nil]
      constructor
      · rintro ((hacc | h0) | ⟨j, hj, hfj⟩)
        · exact Or.inl hacc
        · exact Or.inr ⟨0, Nat.zero_lt_succ m, by simpa using h0⟩
        · exact Or.inr ⟨j + 1, Nat.succ_lt_succ hj, by simpa [List.replicate_succ', List.append_assoc] using hfj⟩
      · rintro (hacc | ⟨j, hj, hfj⟩)
        · exact Or.inl (Or.inl hacc)
        · cases j with
          | zero => exact Or.inl (Or.inr (by simpa using hfj))
          | succ j =>
            exact Or.inr ⟨j, Nat.lt_of_succ_lt_succ hj, by simpa [List.replicate_succ', List.append_assoc] using hfj⟩

def decList (f : List Bool → Bool) (x : List Bool) : List Bool :=
  let res := (unpairB ((outerStep f)^[(true :: x).length] (pairB [] (pairB [] x)))).1
  sel res [false] [true]

theorem cpt_decList (f : List Bool → Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f) :
    CPT (decList f) := by
  have hcnt : CPT (fun x => true :: x) := cpt_cons1 true cpt_id
  have harg : CPT (fun x => pairB [] (pairB [] x)) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) cpt_id)
  have hres : CPT (fun x => (unpairB ((outerStep f)^[(true :: x).length] (pairB [] (pairB [] x)))).1) :=
    cpt_unpairB1_1 (cpt_iterGrow (cpt_outerStep f hf) 6 (outerStep_len f) hcnt harg)
  exact cpt_sel hres (cpt_const [false]) (cpt_const [true])

def dec (f : List Bool → Bool) (x : List Bool) : Bool :=
  (decList f x ++ []).all id

theorem cpt_dec (f : List Bool → Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (dec f) := by
  have hat : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (fun p : List Bool × List Bool => (p.1 ++ p.2).all id) :=
    allTrue_polyTime
  exact cpt_comp (f := fun x => (decList f x, [])) (g := fun p => (p.1 ++ p.2).all id)
    (cpt_pair (cpt_decList f hf) (cpt_const [])) hat

theorem dec_eq_true_iff (f : List Bool → Bool) (x : List Bool) :
    dec f x = true ↔
      ∃ i ≤ x.length, f (x.take i ++ [true, false] ++ x.drop i) = true := by
  simp only [dec, decList, List.length_cons]
  obtain ⟨acc', h1, h2⟩ := outerStep_iter_spec f (x.length + 1) [] [] x
  rw [h1, unpairB_pairB]
  have hsel : (sel acc' [false] [true] ++ []).all id = true ↔ acc' ≠ [] := by
    by_cases h : acc' = [] <;> simp [sel, h]
  rw [hsel, h2]
  simp only [ne_eq, not_true_eq_false, false_or, List.append_nil]
  constructor
  · rintro ⟨i, hi, hloop⟩
    have hile : i ≤ x.length := Nat.lt_succ_iff.mp hi
    have hlen : (List.replicate i true).length ≤ x.length := by simpa using hile
    have hcf : checkFlag f x (List.replicate i true) ≠ [] ↔
        f (cand x (List.replicate i true)) = true := by
      cases hf : f (cand x (List.replicate i true)) <;> simp [checkFlag, hf]
    rw [ne_eq] at hcf
    rw [hcf, cand_eq x (List.replicate i true) hlen, List.length_replicate] at hloop
    exact ⟨i, hile, hloop⟩
  · rintro ⟨i, hi, hfi⟩
    refine ⟨i, Nat.lt_succ_of_le hi, ?_⟩
    have hlen : (List.replicate i true).length ≤ x.length := by simpa using hi
    have hcf : checkFlag f x (List.replicate i true) ≠ [] ↔
        f (cand x (List.replicate i true)) = true := by
      cases hf : f (cand x (List.replicate i true)) <;> simp [checkFlag, hf]
    rw [ne_eq] at hcf
    rw [hcf, cand_eq x (List.replicate i true) hlen, List.length_replicate]
    exact hfi

theorem del_block_iff (L : Language Bool) (f : List Bool → Bool)
    (hf : ∀ x : List Bool, x ∈ L ↔ f x = true) (x : List Bool) :
    (∃ u v : List Bool, x = u ++ v ∧ u ++ [true, false] ++ v ∈ L) ↔ dec f x = true := by
  rw [dec_eq_true_iff]
  constructor
  · rintro ⟨u, v, rfl, hmem⟩
    refine ⟨u.length, by simp, ?_⟩
    simp only [List.take_left, List.drop_left]
    exact (hf _).mp hmem
  · rintro ⟨i, hi, hfi⟩
    refine ⟨x.take i, x.drop i, (List.take_append_drop i x).symm, (hf _).mpr hfi⟩

end PvsNP.Units.tc_closure_del_block_p_aux

theorem PvsNP.Units.tc_closure_del_block_p : ∀ L : Language Bool, L ∈ PvsNP.P → ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ++ [true, false] ++ v ∈ L} : Language Bool) ∈ PvsNP.P := by
  intro L hL
  obtain ⟨f, hfcpt, hfdec⟩ := hL
  exact ⟨PvsNP.Units.tc_closure_del_block_p_aux.dec f,
    PvsNP.Units.tc_closure_del_block_p_aux.cpt_dec f hfcpt,
    fun x => PvsNP.Units.tc_closure_del_block_p_aux.del_block_iff L f hfdec x⟩
