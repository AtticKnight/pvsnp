import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_padded_test_exp
import PvsNP.Units.m2_eq_polytime

namespace PvsNP.Units.tc_exp_hom

open Turing
open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private theorem cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

def homPiece (h : Bool → List Bool) (r : List Bool) : List Bool :=
  sel r [] (sel (hd r) (h false) (h true))

def homMapStep (h : Bool → List Bool) (s : List Bool) : List Bool :=
  pairB (unpairB s).1.tail ((unpairB s).2 ++ homPiece h (unpairB s).1)

theorem homPiece_cons (h : Bool → List Bool) (b : Bool) (r : List Bool) :
    homPiece h (b :: r) = h b := by
  cases b <;> simp [homPiece, sel, hd]

theorem homMapStep_pairB (h : Bool → List Bool) (b : Bool) (r o : List Bool) :
    homMapStep h (pairB (b :: r) o) = pairB r (o ++ h b) := by
  simp only [homMapStep, unpairB_pairB, List.tail_cons, homPiece_cons]

theorem homMap_run (h : Bool → List Bool) :
    ∀ (r o : List Bool), (homMapStep h)^[r.length] (pairB r o) = pairB [] (o ++ r.flatMap h)
  | [], o => by simp
  | b :: r, o => by
    rw [List.length_cons, Function.iterate_succ_apply, homMapStep_pairB, homMap_run h r]
    simp [List.append_assoc]

theorem homMapStep_len (h : Bool → List Bool) (s : List Bool) :
    (homMapStep h s).length ≤ s.length + ((h false).length + (h true).length + 1) := by
  have h1 := unpairB_length s
  have h2 : (homPiece h (unpairB s).1).length ≤ (h false).length + (h true).length := by
    unfold homPiece sel
    split_ifs <;> first | omega | simp
  simp only [homMapStep, pairB_length, List.length_append, List.length_tail]
  omega

theorem cpt_homMapStep (h : Bool → List Bool) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (homMapStep h) := by
  have hR : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hO : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hRt := cpt_comp hR cpt_tail
  have hHd := cpt_comp hR cpt_hd
  have hP := cpt_sel hR (cpt_const []) (cpt_sel hHd (cpt_const (h false)) (cpt_const (h true)))
  have hO' := cpt_app2 hO hP
  exact cptp (cpt_pairB2 hRt hO') (fun _ => rfl)

theorem cpt_flatMap (h : Bool → List Bool) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x.flatMap h) := by
  have hIter := cpt_iterGrow (cpt_homMapStep h) ((h false).length + (h true).length + 1)
    (homMapStep_len h) cpt_id (cpt_pairB2 cpt_id (cpt_const []))
  refine cptp (cpt_unpairB2_1 hIter) (fun x => ?_)
  show (unpairB ((homMapStep h)^[x.length] (pairB x []))).2 = x.flatMap h
  rw [homMap_run h x []]
  simp [unpairB_pairB]

private theorem sel_bflag_and (b1 b2 : Bool) :
    sel (bflag b1) [] (bflag b2) = bflag (b1 && b2) := by
  cases b1 <;> cases b2 <;> rfl

def homTest (h : Bool → List Bool) (c : Code) (Tclk x y : List Bool) : Bool :=
  decide (y.flatMap h = x) && V (pairB (encCode c) (pairB y Tclk), [])

def homStep (h : Bool → List Bool) (c : Code) (s : List Bool) : List Bool :=
  pairB (unpairB s).1
    (pairB (succB (unpairB (unpairB s).2).1)
      ((unpairB (unpairB s).2).2 ++
        bflag (homTest h c (unpairB (unpairB s).1).1 (unpairB (unpairB s).1).2
          (unpairB (unpairB s).2).1)))

def homSrch (h : Bool → List Bool) (c : Code) (Tclk x cnt : List Bool) : List Bool :=
  (unpairB (unpairB ((homStep h c)^[cnt.length] (pairB (pairB Tclk x) (pairB [] [])))).2).2

def homPredStr (h : Bool → List Bool) (c : Code) (d : ℕ) (s : List Bool) : Bool :=
  !(homSrch h c (un (d * (hd (unpairB s).1).length + d)) (unpairB s).2 (hd (unpairB s).1)).isEmpty

def homPred (h : Bool → List Bool) (c : Code) (d : ℕ) (p : List Bool × List Bool) : Bool :=
  homPredStr h c d (pairB p.1 p.2)

theorem homStep_length (h : Bool → List Bool) (c : Code) (s : List Bool) :
    (homStep h c s).length ≤ s.length + 5 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have h3 := bf_succB_length (unpairB (unpairB s).2).1
  have h4 := bf_bflag_length (homTest h c (unpairB (unpairB s).1).1 (unpairB (unpairB s).1).2
    (unpairB (unpairB s).2).1)
  unfold homStep
  rw [pairB_length, pairB_length, List.length_append]
  omega

theorem cpt_homStep (h : Bool → List Bool) (c : Code) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (homStep h c) := by
  have hTx : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).1) := cpt_unpairB1
  have hTclk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).1).1) := cpt_unpairB1_1 hTx
  have hX : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).1).2) := cpt_unpairB2_1 hTx
  have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hY : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).1) := cpt_unpairB1_1 h2
  have hFl : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2) := cpt_unpairB2_1 h2
  have hEq : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s => decide ((unpairB (unpairB s).2).1.flatMap h = (unpairB (unpairB s).1).2)) :=
    cpt_comp (cpt_pair (cpt_comp hY (cpt_flatMap h)) hX) PvsNP.Units.m2_eq_polytime
  have hV : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s => V (pairB (encCode c)
        (pairB (unpairB (unpairB s).2).1 (unpairB (unpairB s).1).1), [])) :=
    cpt_comp (cpt_pair (cpt_pairB2 (cpt_const (encCode c)) (cpt_pairB2 hY hTclk)) (cpt_const []))
      (cpt_V cpt_sstep)
  have hb1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => bflag (decide ((unpairB (unpairB s).2).1.flatMap h = (unpairB (unpairB s).1).2))) :=
    cptp (cpt_bitFlag hEq) (fun _ => rfl)
  have hb2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => bflag (V (pairB (encCode c)
        (pairB (unpairB (unpairB s).2).1 (unpairB (unpairB s).1).1), []))) :=
    cptp (cpt_bitFlag hV) (fun _ => rfl)
  have hb : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => bflag (homTest h c (unpairB (unpairB s).1).1 (unpairB (unpairB s).1).2
        (unpairB (unpairB s).2).1)) :=
    cptp (cpt_sel hb1 (cpt_const []) hb2) (fun s => sel_bflag_and _ _)
  have hSucc : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => succB (unpairB (unpairB s).2).1) := cpt_comp hY bf_cpt_succB
  exact cptp (cpt_pairB2 hTx (cpt_pairB2 hSucc (cpt_app2 hFl hb))) (fun _ => rfl)

theorem cpt_homPredStr (h : Bool → List Bool) (c : Code) (d : ℕ) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool (homPredStr h c d) := by
  have hCnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => hd (unpairB s).1) := cpt_hd1 cpt_unpairB1
  have hX : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hTclk : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => un (d * (hd (unpairB s).1).length + d)) := by
    have h1 := cpt_comp hCnt (L055 (Polynomial.C d * Polynomial.X + Polynomial.C d))
    exact cptp h1 (fun s => by simp [un])
  have hInit := cpt_pairB2 (cpt_pairB2 hTclk hX) (cpt_const (pairB [] []))
  have hSrch := cpt_unpairB2_1 (cpt_unpairB2_1
    (cpt_iterGrow (cpt_homStep h c) 5 (homStep_length h c) hCnt hInit))
  exact cptp (cpt_comp hSrch bf_cpt_neL) (fun _ => rfl)

theorem cpt_homPred (h : Bool → List Bool) (c : Code) (d : ℕ) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (homPred h c d) :=
  cptp (cpt_comp cpt_pairB (cpt_homPredStr h c d)) (fun _ => rfl)

theorem homStep_pair (h : Bool → List Bool) (c : Code) (Tclk x y fl : List Bool) :
    homStep h c (pairB (pairB Tclk x) (pairB y fl)) =
      pairB (pairB Tclk x) (pairB (succB y) (fl ++ bflag (homTest h c Tclk x y))) := by
  simp [homStep, unpairB_pairB]

theorem homStep_iter (h : Bool → List Bool) (c : Code) (Tclk x : List Bool) (m : ℕ) :
    ∀ y fl : List Bool, ∃ fl' : List Bool,
      (homStep h c)^[m] (pairB (pairB Tclk x) (pairB y fl)) =
        pairB (pairB Tclk x) (pairB (succB^[m] y) fl') ∧
        (fl' = [] ↔ fl = [] ∧ ∀ j < m, homTest h c Tclk x (succB^[j] y) = false) := by
  induction m with
  | zero => intro y fl; exact ⟨fl, rfl, by simp⟩
  | succ m ih =>
    intro y fl
    obtain ⟨fl', h1, h2⟩ := ih (succB y) (fl ++ bflag (homTest h c Tclk x y))
    refine ⟨fl', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, homStep_pair, h1, Function.iterate_succ_apply]
    · rw [h2, List.append_eq_nil_iff, bflag_eq_nil, Nat.forall_lt_succ_left, and_assoc]
      simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply]

theorem homSrch_eq_nil (h : Bool → List Bool) (c : Code) (Tclk x cnt : List Bool) :
    homSrch h c Tclk x cnt = [] ↔ ∀ j < cnt.length, homTest h c Tclk x (cand j) = false := by
  obtain ⟨fl', h1, h2⟩ := homStep_iter h c Tclk x cnt.length [] []
  rw [homSrch, h1]
  simpa [unpairB_pairB, cand] using h2

theorem length_le_flatMap (h : Bool → List Bool) (hh : ∀ b, h b ≠ []) :
    ∀ y : List Bool, y.length ≤ (y.flatMap h).length
  | [] => le_rfl
  | b :: y => by
    have hb : 1 ≤ (h b).length := List.length_pos_of_ne_nil (hh b)
    have ih := length_le_flatMap h hh y
    simp only [List.flatMap_cons, List.length_cons, List.length_append]
    omega

theorem time_le_budget (k n m : ℕ) (hmn : m ≤ n) :
    2 ^ (m ^ k) + k ≤ 2 ^ ((n + 1) ^ max k 1) + max k 1 := by
  have hk : k ≤ max k 1 := le_max_left k 1
  have hexp : m ^ k ≤ (n + 1) ^ max k 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp only [pow_zero]
      exact Nat.one_le_pow _ _ (by omega)
    · exact (Nat.pow_le_pow_left (by omega) k).trans
        (Nat.pow_le_pow_right (by omega) hk)
  have hpow : 2 ^ (m ^ k) ≤ 2 ^ ((n + 1) ^ max k 1) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  omega

theorem idx_lt_budget (k n : ℕ) (y : List Bool) (hy : y.length ≤ n) :
    idx y < 2 ^ ((n + 1) ^ max k 1) + max k 1 := by
  have h1 : idx y + 2 ≤ 2 ^ (n + 1) := idx_lt_of_length_le hy
  have h2 : n + 1 ≤ (n + 1) ^ max k 1 :=
    Nat.le_self_pow (by have := le_max_right k 1; omega) (n + 1)
  have h3 : 2 ^ (n + 1) ≤ 2 ^ ((n + 1) ^ max k 1) :=
    Nat.pow_le_pow_right (by norm_num) h2
  omega

theorem exp_hom_main (h : Bool → List Bool) (hh : ∀ b, h b ≠ []) (L : Language Bool)
    (hL : ∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) :
    ∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ y ∈ L, x = y.flatMap h) ↔ f x = true) ∧
        ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  obtain ⟨k, f, M, hf, htime⟩ := hL
  obtain ⟨c, d, hc⟩ := compileBool M.tm M.inputAlphabet M.outputAlphabet
  let K : ℕ := max k 1
  have hu : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => true :: x) := cpt_cons1 true cpt_id
  have hv : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x) := cpt_id
  obtain ⟨j, M', hM'⟩ := PvsNP.Units.m2_padded_test_exp K
    (fun x : List Bool => true :: x) (fun x : List Bool => x) (homPred h c d)
    hu hv (cpt_homPred h c d)
  let g : List Bool → Bool := fun x =>
    homPred h c d (List.replicate (2 ^ ((true :: x).length ^ K) + K) true ++ false :: (true :: x), x)
  refine ⟨j, g, M', fun x => ?_, hM'⟩
  let t : ℕ := 2 ^ ((x.length + 1) ^ K) + K
  have hV_iff : ∀ y : List Bool, y.length ≤ x.length →
      (V (pairB (encCode c) (pairB y (un (d * t + d))), []) = true ↔ f y = true) := by
    intro y hy
    have hsteps : (M.outputsFun y).steps ≤ t := by
      have h1 : (M.outputsFun y).steps ≤ M.time y.length := (M.outputsFun y).steps_le_m
      have h2 : M.time y.length ≤ 2 ^ (y.length ^ k) + k := htime y.length
      have h3 : 2 ^ (y.length ^ k) + k ≤ t := time_le_budget k x.length y.length hy
      exact h1.trans (h2.trans h3)
    have hcw := hc y (f y) (M.outputsFun y).steps (M.outputsFun y).evals_in_steps
    have hle_steps : d * (M.outputsFun y).steps + d ≤ d * t + d := by
      have := Nat.mul_le_mul_left d hsteps
      omega
    have hcw' := Code.outputsWithin_mono c _ hle_steps _ hcw
    rw [V_spec]
    simp only [List.map_nil, List.append_nil, List.length_nil, Nat.zero_le, true_and]
    constructor
    · intro h1
      have heq : [1] = [bitCode (f y)] := h1.2.symm.trans hcw'.2
      cases hb : f y with
      | false => rw [hb] at heq; simp [bitCode] at heq
      | true => rfl
    · intro hb
      rw [hb] at hcw'
      simpa [bitCode] using hcw'
  have htest : ∀ y : List Bool,
      homTest h c (un (d * t + d)) x y = true ↔ y ∈ L ∧ x = y.flatMap h := by
    intro y
    unfold homTest
    rw [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hmap, hV⟩
      have hy : y.length ≤ x.length := by
        rw [← hmap]; exact length_le_flatMap h hh y
      exact ⟨(hf y).mpr ((hV_iff y hy).mp hV), hmap.symm⟩
    · rintro ⟨hyL, hmap⟩
      have hy : y.length ≤ x.length := by
        rw [hmap]; exact length_le_flatMap h hh y
      exact ⟨hmap.symm, (hV_iff y hy).mpr ((hf y).mp hyL)⟩
  have hgx : g x = true ↔ ¬ homSrch h c (un (d * t + d)) x (un t) = [] := by
    have hlen : (true :: x).length = x.length + 1 := rfl
    have hhd : hd (List.replicate t true ++ false :: (true :: x)) = un t := hd_un t (true :: x)
    simp only [g, homPred, homPredStr, unpairB_pairB, hlen]
    change !(homSrch h c (un (d * (hd (List.replicate t true ++ false :: (true :: x))).length + d))
      x (hd (List.replicate t true ++ false :: (true :: x)))).isEmpty = true ↔ _
    rw [hhd, un_length]
    cases homSrch h c (un (d * t + d)) x (un t) <;> simp
  rw [hgx, homSrch_eq_nil, un_length]
  constructor
  · rintro ⟨y, hyL, hmap⟩ hall
    have hy : y.length ≤ x.length := by
      rw [hmap]; exact length_le_flatMap h hh y
    have hlt : idx y < t := idx_lt_budget k x.length y hy
    have hfalse := hall (idx y) hlt
    rw [cand_idx] at hfalse
    have htrue := (htest y).mpr ⟨hyL, hmap⟩
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue
  · intro hnot
    by_contra hnone
    apply hnot
    intro j_idx _
    cases hv : homTest h c (un (d * t + d)) x (cand j_idx) with
    | false => rfl
    | true =>
      obtain ⟨hyL, hmap⟩ := (htest (cand j_idx)).mp hv
      exact False.elim (hnone ⟨cand j_idx, hyL, hmap⟩)

end PvsNP.Units.tc_exp_hom

theorem PvsNP.Units.tc_exp_hom :
    ∀ h : Bool → List Bool, (∀ b, h b ≠ []) → ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ y ∈ L, x = y.flatMap h) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_hom.exp_hom_main
