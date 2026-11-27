import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_bounded_unary_search_polytime

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_abelian_square_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  rfl

theorem encodeString_eq :
    PvsNP.encodeString = (fun x : List Bool => x) := by
  funext x
  rfl

def dropMeas (_ : List Bool) : ℕ := 0

theorem dropMeas_step (s : List Bool) :
    dropMeas s.tail ≤ dropMeas s := le_rfl

theorem dropMeas_linear (s : List Bool) :
    dropMeas s ≤ 1 * s.length + 1 := by
  unfold dropMeas; omega

theorem tail_len (s : List Bool) :
    s.tail.length ≤ s.length + dropMeas s := by
  simp [dropMeas]

theorem tail_iter_nil : ∀ k : ℕ, List.tail^[k] ([] : List Bool) = []
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply, List.tail_nil, tail_iter_nil k]

theorem tail_iter_eq : ∀ (k : ℕ) (x : List Bool), List.tail^[k] x = x.drop k
  | 0, x => by simp
  | k + 1, [] => by simp [tail_iter_nil]
  | k + 1, _ :: xs => by
    rw [Function.iterate_succ_apply, List.tail_cons, tail_iter_eq k xs, List.drop_succ_cons]

theorem cpt_dropPair :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB s).1.drop (unpairB s).2.length) := by
  have htail : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString List.tail :=
    cpt_tail1 cpt_id
  obtain ⟨cs⟩ := htail
  have hiter : PvsNP.PolyTimeComputable
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => List.tail^[p.2.length] p.1) :=
    Iter.iter_polyTime_measure List.tail cs dropMeas 1
      dropMeas_step tail_len dropMeas_linear
  have h1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).1) := cpt_unpairB1
  have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).2) := cpt_unpairB2
  have hc := PvsNP.Units.m2_polytime_comp PvsNP.encodeString
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
    _ _ (cpt_pair h1 h2) hiter
  have heq : ((fun p : List Bool × List Bool => List.tail^[p.2.length] p.1) ∘
      (fun s : List Bool => ((unpairB s).1, (unpairB s).2))) =
      (fun s : List Bool => (unpairB s).1.drop (unpairB s).2.length) := by
    funext s
    simp [tail_iter_eq]
  rwa [heq] at hc

def sufOfStr (s : List Bool) : List Bool :=
  (unpairB s).1.drop (unpairB s).2.length

def prefOfStr (s : List Bool) : List Bool :=
  (((unpairB s).1.reverse).drop (sufOfStr s).length).reverse

theorem prefOfStr_eq (x w : List Bool) :
    prefOfStr (pairB x w) = x.take w.length := by
  unfold prefOfStr sufOfStr
  simp only [unpairB_pairB]
  have hx : x = x.take w.length ++ x.drop w.length := (List.take_append_drop w.length x).symm
  have hrev : x.reverse = (x.drop w.length).reverse ++ (x.take w.length).reverse := by
    conv_lhs => rw [hx]
    exact List.reverse_append
  rw [hrev]
  have hlen : (x.drop w.length).length = (x.drop w.length).reverse.length :=
    (List.length_reverse).symm
  rw [hlen, List.drop_left, List.reverse_reverse]

theorem cpt_prefOfStr :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString prefOfStr := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s : List Bool => (unpairB s).1) := cpt_unpairB1
  have hrev1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    _ List.reverse h1 PvsNP.Units.m2_reverse_polytime
  have hp : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => pairB ((unpairB s).1.reverse) (sufOfStr s)) :=
    cpt_pairB2 hrev1 cpt_dropPair
  have hdrop := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    _ _ hp cpt_dropPair
  have hrev2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    _ List.reverse hdrop PvsNP.Units.m2_reverse_polytime
  have heq : (List.reverse ∘ ((fun z : List Bool => (unpairB z).1.drop (unpairB z).2.length) ∘
      (fun s : List Bool => pairB ((unpairB s).1.reverse) (sufOfStr s)))) = prefOfStr := by
    funext s
    simp [prefOfStr, unpairB_pairB]
  rwa [heq] at hrev2

def onesOf (b : Bool) (l : List Bool) : List Bool :=
  l.filterMap (fun c => if c == b then some true else none)

theorem onesOf_eq_replicate (b : Bool) (l : List Bool) :
    onesOf b l = List.replicate (l.count b) true := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> cases b <;> simp [onesOf, List.replicate_succ] at ih ⊢ <;> exact ih

theorem cpt_onesOf (b : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (onesOf b) := by
  rw [encodeString_eq]
  exact filterMap_polyTime _ _ _ (fun c : Bool => if c == b then some true else none) (fun _ => rfl)

def eqOnesPair (b : Bool) (p : List Bool × List Bool) : Bool :=
  decide (onesOf b (prefOfStr (pairB p.1 p.2)) = onesOf b (sufOfStr (pairB p.1 p.2)))

def abelCheck (p : List Bool × List Bool) : Bool :=
  eqOnesPair true p && eqOnesPair false p

theorem cpt_eqOnesPair (b : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (eqOnesPair b) := by
  have hL := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    prefOfStr (onesOf b) cpt_prefOfStr (cpt_onesOf b)
  have hR := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
    sufOfStr (onesOf b) cpt_dropPair (cpt_onesOf b)
  have hp := PvsNP.Units.m2_pair_build_polytime _ _ hL hR
  have hcStr := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
    _ (fun p : List Bool × List Bool => decide (p.1 = p.2))
    hp PvsNP.Units.m2_eq_polytime
  have hpB : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => pairB p.1 p.2) := by
    rw [← encodePair_eq, encodeString_eq]
    exact cpt_pairB
  have hc := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => pairB p.1 p.2) _ hpB hcStr
  have heq : (((fun p : List Bool × List Bool => decide (p.1 = p.2)) ∘
      (fun x : List Bool => ((onesOf b ∘ prefOfStr) x, (onesOf b ∘ sufOfStr) x))) ∘
      (fun p : List Bool × List Bool => pairB p.1 p.2)) = eqOnesPair b := by
    funext p; rfl
  rwa [heq] at hc

theorem cpt_abelCheck :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer abelCheck :=
  PvsNP.Units.m2_tm_pair_bool_combine (· && ·) _ _ (cpt_eqOnesPair true) (cpt_eqOnesPair false)

theorem main_proof :
    ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ List.Perm u v} :
      Language Bool) ∈ PvsNP.P := by
  have hdec := PvsNP.Units.m2_bounded_unary_search_polytime abelCheck cpt_abelCheck
  refine ⟨_, hdec, fun x => ?_⟩
  change (∃ u v : List Bool, x = u ++ v ∧ List.Perm u v) ↔
    ((List.range (x.length + 1)).any (fun i => abelCheck (x, List.replicate i true))) = true
  rw [List.any_eq_true]
  simp only [List.mem_range]
  constructor
  · rintro ⟨u, v, rfl, hperm⟩
    refine ⟨u.length, by simp, ?_⟩
    unfold abelCheck eqOnesPair
    have hpref : prefOfStr (pairB (u ++ v) (List.replicate u.length true)) = u := by
      rw [prefOfStr_eq (u ++ v) (List.replicate u.length true)]
      simp
    have hsuf : sufOfStr (pairB (u ++ v) (List.replicate u.length true)) = v := by
      unfold sufOfStr
      simp [unpairB_pairB]
    rw [hpref, hsuf]
    simp [onesOf_eq_replicate, hperm.count_eq]
  · rintro ⟨i, hi, hchk⟩
    refine ⟨x.take i, x.drop i, (List.take_append_drop i x).symm, ?_⟩
    unfold abelCheck eqOnesPair at hchk
    have hpref : prefOfStr (pairB x (List.replicate i true)) = x.take i := by
      rw [prefOfStr_eq x (List.replicate i true)]
      simp
    have hsuf : sufOfStr (pairB x (List.replicate i true)) = x.drop i := by
      unfold sufOfStr
      simp [unpairB_pairB]
    rw [hpref, hsuf] at hchk
    simp only [Bool.and_eq_true, decide_eq_true_eq, onesOf_eq_replicate] at hchk
    have hct : (x.take i).count true = (x.drop i).count true := by
      have := congrArg List.length hchk.1
      simpa using this
    have hcf : (x.take i).count false = (x.drop i).count false := by
      have := congrArg List.length hchk.2
      simpa using this
    have _ := hi
    rw [List.perm_iff_count]
    intro b
    cases b
    · exact hcf
    · exact hct

end PvsNP.Units.tl_lang_abelian_square_p

/-- The abelian squares are in P (TM2). -/
theorem PvsNP.Units.tl_lang_abelian_square_p :
    ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ List.Perm u v} :
      Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_abelian_square_p.main_proof
