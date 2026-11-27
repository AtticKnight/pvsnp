import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_tm_iterate_measure

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_rev_factor_p_aux

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

abbrev CPT (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f

private def tk1D : Bool → Bool → Bool × Option Bool
  | true, b => (false, some b)
  | false, _ => (false, none)

private theorem tk1D_false (l : List Bool) : fstRun tk1D (fun _ => none) false l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, tk1D, ih]

private theorem tk1D_true (l : List Bool) : fstRun tk1D (fun _ => none) true l = l.take 1 := by
  cases l with
  | nil => rfl
  | cons b l => simp [fstRun, tk1D, tk1D_false]

theorem cpt_take1 : CPT (fun s : List Bool => s.take 1) :=
  fst_polyTime _ _ _ tk1D (fun _ => none) true (fun s => (tk1D_true s).symm)

def revStep (s : List Bool) : List Bool :=
  pairB ((unpairB s).2.take 1 ++ (unpairB s).1) (unpairB s).2.tail

theorem cpt_revStep : CPT revStep :=
  cpt_pairB2 (cpt_app2 (cpt_comp cpt_unpairB2 cpt_take1) cpt_unpairB1) (cpt_tail1 cpt_unpairB2)

theorem unpairB_len (s : List Bool) :
    2 * (unpairB s).1.length + (unpairB s).2.length ≤ s.length := by
  have htd : (s.takeWhile id).length + (s.dropWhile id).length = s.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  simp only [unpairB, List.length_take, List.length_drop, List.length_tail]
  omega

theorem revStep_len (s : List Bool) : (revStep s).length ≤ s.length + 3 := by
  have hu := unpairB_len s
  simp only [revStep, pairB, un, List.length_append, List.length_cons,
    List.length_replicate, List.length_take, List.length_tail]
  omega

def revIter (c y : List Bool) : List Bool :=
  revStep^[c.length] (pairB [] y)

theorem cpt_revIter {c y : List Bool → List Bool} (hc : CPT c) (hy : CPT y) :
    CPT (fun s => revIter (c s) (y s)) :=
  cpt_iterGrow cpt_revStep 3 revStep_len hc (cpt_pairB2 (cpt_const []) hy)

theorem revIter_spec (m : ℕ) (acc y : List Bool) (hm : m ≤ y.length) :
    revStep^[m] (pairB acc y) = pairB ((y.take m).reverse ++ acc) (y.drop m) := by
  induction m generalizing acc y with
  | zero => simp
  | succ m ih =>
    cases y with
    | nil => simp at hm
    | cons b y' =>
      rw [Function.iterate_succ_apply]
      have hstep : revStep (pairB acc (b :: y')) = pairB (b :: acc) y' := by
        simp [revStep, unpairB_pairB]
      rw [hstep, ih (b :: acc) y' (by simpa using hm)]
      simp

theorem revIter_pair (c y : List Bool) (hc : c.length ≤ y.length) :
    revIter c y = pairB (y.take c.length).reverse (y.drop c.length) := by
  simpa [revIter] using revIter_spec c.length [] y hc

def cand (x i_str k_str : List Bool) : List Bool :=
  let p1 := revIter i_str x
  let u_rev := (unpairB p1).1
  let vw := (unpairB p1).2
  let u := (unpairB (revIter i_str u_rev)).1
  let p2 := revIter k_str vw
  let v_rev := (unpairB p2).1
  let w := (unpairB p2).2
  u ++ v_rev ++ w

theorem cpt_cand {x i_str k_str : List Bool → List Bool} (hx : CPT x) (hi : CPT i_str) (hk : CPT k_str) :
    CPT (fun s => cand (x s) (i_str s) (k_str s)) := by
  have hp1 : CPT (fun s => revIter (i_str s) (x s)) := cpt_revIter hi hx
  have hu_rev : CPT (fun s => (unpairB (revIter (i_str s) (x s))).1) := cpt_unpairB1_1 hp1
  have hvw : CPT (fun s => (unpairB (revIter (i_str s) (x s))).2) := cpt_unpairB2_1 hp1
  have hu : CPT (fun s => (unpairB (revIter (i_str s) (unpairB (revIter (i_str s) (x s))).1)).1) :=
    cpt_unpairB1_1 (cpt_revIter hi hu_rev)
  have hp2 : CPT (fun s => revIter (k_str s) (unpairB (revIter (i_str s) (x s))).2) :=
    cpt_revIter hk hvw
  have hv_rev : CPT (fun s => (unpairB (revIter (k_str s) (unpairB (revIter (i_str s) (x s))).2)).1) :=
    cpt_unpairB1_1 hp2
  have hw : CPT (fun s => (unpairB (revIter (k_str s) (unpairB (revIter (i_str s) (x s))).2)).2) :=
    cpt_unpairB2_1 hp2
  exact cpt_app2 (cpt_app2 hu hv_rev) hw

theorem cand_eq (x i_str k_str : List Bool) (h : i_str.length + k_str.length ≤ x.length) :
    cand x i_str k_str =
      x.take i_str.length ++ ((x.drop i_str.length).take k_str.length).reverse ++
        (x.drop i_str.length).drop k_str.length := by
  have hi : i_str.length ≤ x.length := by omega
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
  have hk : k_str.length ≤ (x.drop i_str.length).length := by
    rw [List.length_drop]; omega
  have hp2 : revIter k_str (x.drop i_str.length) =
      pairB ((x.drop i_str.length).take k_str.length).reverse
        ((x.drop i_str.length).drop k_str.length) :=
    revIter_pair k_str _ hk
  simp only [cand, hp1, unpairB_pairB, hu_rev, htake_all, List.reverse_reverse, hp2]

def checkFlag (f : List Bool → Bool) (x i_str k_str : List Bool) : List Bool :=
  if f (cand x i_str k_str) then [true] else []

theorem cpt_checkFlag (f : List Bool → Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f)
    {x i_str k_str : List Bool → List Bool} (hx : CPT x) (hi : CPT i_str) (hk : CPT k_str) :
    CPT (fun s => checkFlag f (x s) (i_str s) (k_str s)) := by
  have hbf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun a => if f a then [true] else []) :=
    cpt_bitFlag hf
  exact cpt_comp (cpt_cand hx hi hk) hbf

def innerStep (f : List Bool → Bool) (s : List Bool) : List Bool :=
  let acc := (unpairB s).1
  let r := (unpairB s).2
  let k_str := (unpairB r).1
  let xi := (unpairB r).2
  let x := (unpairB xi).1
  let i_str := (unpairB xi).2
  let bit := checkFlag f x i_str k_str
  let acc' := sel acc bit [true]
  pairB acc' (pairB (true :: k_str) xi)

theorem cpt_innerStep (f : List Bool → Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f) :
    CPT (innerStep f) := by
  have hacc : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hr : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hk : CPT (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hr
  have hxi : CPT (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hr
  have hx : CPT (fun s => (unpairB (unpairB (unpairB s).2).2).1) := cpt_unpairB1_1 hxi
  have hi : CPT (fun s => (unpairB (unpairB (unpairB s).2).2).2) := cpt_unpairB2_1 hxi
  have hbit := cpt_checkFlag f hf hx hi hk
  have hacc' := cpt_sel hacc hbit (cpt_const [true])
  exact cpt_pairB2 hacc' (cpt_pairB2 (cpt_cons1 true hk) hxi)

theorem sel_bit_len (acc : List Bool) (b : Bool) :
    (sel acc (if b then [true] else []) [true]).length ≤ 1 := by
  by_cases h : acc = []
  · cases b <;> simp [sel, h]
  · simp [sel, h]

theorem sel_ne_nil (acc bit : List Bool) :
    sel acc bit [true] ≠ [] ↔ acc ≠ [] ∨ bit ≠ [] := by
  by_cases h : acc = []
  · simp [sel, h]
  · simp [sel, h]

theorem innerStep_len (f : List Bool → Bool) (s : List Bool) :
    (innerStep f s).length ≤ s.length + 6 := by
  have h1 := unpairB_len s
  have h2 := unpairB_len (unpairB s).2
  have hacc : (sel (unpairB s).1
      (checkFlag f (unpairB (unpairB (unpairB s).2).2).1
        (unpairB (unpairB (unpairB s).2).2).2 (unpairB (unpairB s).2).1)
      [true]).length ≤ 1 := by
    simpa [checkFlag] using sel_bit_len (unpairB s).1 _
  simp only [innerStep, pairB, un, List.length_append, List.length_cons,
    List.length_replicate]
  omega

def innerLoop (f : List Bool → Bool) (x i_str : List Bool) : List Bool :=
  let cnt := true :: (unpairB (revIter i_str x)).2
  (unpairB ((innerStep f)^[cnt.length] (pairB [] (pairB [] (pairB x i_str))))).1

theorem cpt_innerLoop (f : List Bool → Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f)
    {x i_str : List Bool → List Bool} (hx : CPT x) (hi : CPT i_str) :
    CPT (fun s => innerLoop f (x s) (i_str s)) := by
  have hcnt : CPT (fun s => true :: (unpairB (revIter (i_str s) (x s))).2) :=
    cpt_cons1 true (cpt_unpairB2_1 (cpt_revIter hi hx))
  have harg : CPT (fun s => pairB [] (pairB [] (pairB (x s) (i_str s)))) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) (cpt_pairB2 hx hi))
  exact cpt_unpairB1_1 (cpt_iterGrow (cpt_innerStep f hf) 6 (innerStep_len f) hcnt harg)

theorem innerLoop_len (f : List Bool → Bool) (x i_str : List Bool) :
    (innerLoop f x i_str).length ≤ 1 := by
  simp only [innerLoop]
  generalize (true :: (unpairB (revIter i_str x)).2).length = m
  cases m with
  | zero => simp [unpairB_pairB]
  | succ m =>
    rw [Function.iterate_succ_apply']
    simp only [innerStep, unpairB_pairB]
    simpa [checkFlag] using sel_bit_len _ _

theorem innerStep_iter_spec (f : List Bool → Bool) (m : ℕ) (acc k_str x i_str : List Bool) :
    ∃ acc',
      (innerStep f)^[m] (pairB acc (pairB k_str (pairB x i_str))) =
        pairB acc' (pairB (List.replicate m true ++ k_str) (pairB x i_str)) ∧
      (acc' ≠ [] ↔ acc ≠ [] ∨ ∃ j < m, f (cand x i_str (List.replicate j true ++ k_str)) = true) := by
  induction m generalizing acc k_str with
  | zero =>
    refine ⟨acc, by simp, by simp⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hstep : innerStep f (pairB acc (pairB k_str (pairB x i_str))) =
        pairB (sel acc (checkFlag f x i_str k_str) [true]) (pairB (true :: k_str) (pairB x i_str)) := by
      simp [innerStep, unpairB_pairB]
    rw [hstep]
    obtain ⟨acc', h1, h2⟩ := ih (sel acc (checkFlag f x i_str k_str) [true]) (true :: k_str)
    refine ⟨acc', ?_, ?_⟩
    · simpa [List.replicate_succ', List.append_assoc] using h1
    · rw [h2, sel_ne_nil]
      have hcf : checkFlag f x i_str k_str ≠ [] ↔ f (cand x i_str k_str) = true := by
        cases hf : f (cand x i_str k_str) <;> simp [checkFlag, hf]
      rw [hcf]
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

theorem innerLoop_spec (f : List Bool → Bool) (x i_str : List Bool) (hi : i_str.length ≤ x.length) :
    innerLoop f x i_str ≠ [] ↔
      ∃ k ≤ (x.drop i_str.length).length,
        f (x.take i_str.length ++ ((x.drop i_str.length).take k).reverse ++
          (x.drop i_str.length).drop k) = true := by
  have hp1 : (unpairB (revIter i_str x)).2 = x.drop i_str.length := by
    rw [revIter_pair i_str x hi, unpairB_pairB]
  simp only [innerLoop, hp1, List.length_cons]
  obtain ⟨acc', h1, h2⟩ := innerStep_iter_spec f ((x.drop i_str.length).length + 1) [] [] x i_str
  rw [h1, unpairB_pairB, h2]
  simp only [ne_eq, not_true_eq_false, false_or, List.append_nil]
  constructor
  · rintro ⟨j, hj, hfj⟩
    have hjle : j ≤ (x.drop i_str.length).length := Nat.lt_succ_iff.mp hj
    have hsum : i_str.length + (List.replicate j true).length ≤ x.length := by
      rw [List.length_replicate, List.length_drop] at *; omega
    rw [cand_eq x i_str (List.replicate j true) hsum, List.length_replicate] at hfj
    exact ⟨j, hjle, hfj⟩
  · rintro ⟨k, hk, hfk⟩
    refine ⟨k, Nat.lt_succ_of_le hk, ?_⟩
    have hsum : i_str.length + (List.replicate k true).length ≤ x.length := by
      rw [List.length_replicate, List.length_drop] at *; omega
    rw [cand_eq x i_str (List.replicate k true) hsum, List.length_replicate]
    exact hfk

def outerStep (f : List Bool → Bool) (s : List Bool) : List Bool :=
  let acc := (unpairB s).1
  let ix := (unpairB s).2
  let i_str := (unpairB ix).1
  let x := (unpairB ix).2
  let bit := innerLoop f x i_str
  let acc' := sel acc bit [true]
  pairB acc' (pairB (true :: i_str) x)

theorem cpt_outerStep (f : List Bool → Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer f) :
    CPT (outerStep f) := by
  have hacc : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hix : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hi : CPT (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 hix
  have hx : CPT (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 hix
  have hbit := cpt_innerLoop f hf hx hi
  have hacc' := cpt_sel hacc hbit (cpt_const [true])
  exact cpt_pairB2 hacc' (cpt_pairB2 (cpt_cons1 true hi) hx)

theorem outerStep_len (f : List Bool → Bool) (s : List Bool) :
    (outerStep f s).length ≤ s.length + 6 := by
  have h1 := unpairB_len s
  have h2 := unpairB_len (unpairB s).2
  have hbit := innerLoop_len f (unpairB (unpairB s).2).2 (unpairB (unpairB s).2).1
  have hacc : (sel (unpairB s).1 (innerLoop f (unpairB (unpairB s).2).2 (unpairB (unpairB s).2).1)
      [true]).length ≤ 1 := by
    by_cases h : (unpairB s).1 = []
    · simpa [sel, h] using hbit
    · simp [sel, h]
  simp only [outerStep, pairB, un, List.length_append, List.length_cons,
    List.length_replicate]
  omega

theorem outerStep_iter_spec (f : List Bool → Bool) (m : ℕ) (acc i_str x : List Bool) :
    ∃ acc',
      (outerStep f)^[m] (pairB acc (pairB i_str x)) =
        pairB acc' (pairB (List.replicate m true ++ i_str) x) ∧
      (acc' ≠ [] ↔ acc ≠ [] ∨ ∃ j < m, innerLoop f x (List.replicate j true ++ i_str) ≠ []) := by
  induction m generalizing acc i_str with
  | zero =>
    refine ⟨acc, by simp, by simp⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hstep : outerStep f (pairB acc (pairB i_str x)) =
        pairB (sel acc (innerLoop f x i_str) [true]) (pairB (true :: i_str) x) := by
      simp [outerStep, unpairB_pairB]
    rw [hstep]
    obtain ⟨acc', h1, h2⟩ := ih (sel acc (innerLoop f x i_str) [true]) (true :: i_str)
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
      ∃ i ≤ x.length, ∃ k ≤ (x.drop i).length,
        f (x.take i ++ ((x.drop i).take k).reverse ++ (x.drop i).drop k) = true := by
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
    have hs := innerLoop_spec f x (List.replicate i true) hlen
    rw [ne_eq, List.length_replicate] at hs
    rw [hs] at hloop
    exact ⟨i, hile, hloop⟩
  · rintro ⟨i, hi, k, hk, hfk⟩
    refine ⟨i, Nat.lt_succ_of_le hi, ?_⟩
    have hlen : (List.replicate i true).length ≤ x.length := by simpa using hi
    have hs := innerLoop_spec f x (List.replicate i true) hlen
    rw [ne_eq, List.length_replicate] at hs
    rw [hs]
    exact ⟨k, hk, hfk⟩

theorem rev_factor_iff (L : Language Bool) (f : List Bool → Bool)
    (hf : ∀ x : List Bool, x ∈ L ↔ f x = true) (x : List Bool) :
    (∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w ∈ L) ↔ dec f x = true := by
  rw [dec_eq_true_iff]
  constructor
  · rintro ⟨u, v, w, rfl, hmem⟩
    refine ⟨u.length, by simp, v.length, by simp, ?_⟩
    simp only [List.append_assoc, List.take_left, List.drop_left]
    rw [← List.append_assoc]
    exact (hf _).mp hmem
  · rintro ⟨i, hi, k, hk, hfk⟩
    refine ⟨x.take i, (x.drop i).take k, (x.drop i).drop k, ?_, (hf _).mpr hfk⟩
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

end PvsNP.Units.tc_closure_rev_factor_p_aux

theorem PvsNP.Units.tc_closure_rev_factor_p : ∀ L : Language Bool, L ∈ PvsNP.P → ({x : List Bool | ∃ u v w : List Bool, x = u ++ v ++ w ∧ u ++ v.reverse ++ w ∈ L} : Language Bool) ∈ PvsNP.P := by
  intro L hL
  obtain ⟨f, hfcpt, hfdec⟩ := hL
  exact ⟨PvsNP.Units.tc_closure_rev_factor_p_aux.dec f,
    PvsNP.Units.tc_closure_rev_factor_p_aux.cpt_dec f hfcpt,
    fun x => PvsNP.Units.tc_closure_rev_factor_p_aux.rev_factor_iff L f hfdec x⟩
