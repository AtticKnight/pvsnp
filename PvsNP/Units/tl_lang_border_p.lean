import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_tm_suffix_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_bounded_unary_search_polytime

namespace PvsNP.Units.tl_lang_border_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-- Change the function computed by a polynomial-time computation, pointwise. -/
private theorem cpt_conv {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- The length guard: `u.length + 1 < x.length`, tested on a pair `(x, u)`. -/
private theorem guard_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.2.length + 1 < p.1.length)) := by
  have hpair : ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1, p.2 ++ [true, true])) :=
    cpt_pairG cpt_fst
      (cpt_comp cpt_snd (cpt_app2 cpt_id (cpt_const [true, true])))
  have h := cpt_comp hpair LenCmp.lenLE_polyTime
  refine cpt_conv h ?_
  intro p
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [decide_eq_decide]
  omega

/-- Taking the first `u.length + 1` bits of `x` is polynomial-time. -/
private theorem take_succ_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1.take (p.2.length + 1)) := by
  have hpair : ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.2 ++ [true], p.1)) :=
    cpt_pairG (cpt_comp cpt_snd (cpt_app2 cpt_id (cpt_const [true]))) cpt_fst
  have h := cpt_comp hpair PvsNP.Units.m2_take_drop_length_polytime.1
  refine cpt_conv h ?_
  intro p
  simp only [List.length_append, List.length_cons, List.length_nil]

/-- The suffix test: the first `u.length + 1` bits of `x` end `x`. -/
private theorem suffix_poly :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => (p.1.take (p.2.length + 1)).isSuffixOf p.1) := by
  have hpair : ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1.take (p.2.length + 1), p.1)) :=
    cpt_pairG take_succ_poly cpt_fst
  exact cpt_comp hpair PvsNP.Units.m2_tm_suffix_polytime

/-- The test at unary `i`: length `i + 1` is a proper border length and the
corresponding prefix is a suffix. -/
private def testV (p : List Bool × List Bool) : Bool :=
  decide (p.2.length + 1 < p.1.length) && (p.1.take (p.2.length + 1)).isSuffixOf p.1

private theorem cpt_testV :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer testV := by
  show PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool =>
      decide (p.2.length + 1 < p.1.length) &&
        (p.1.take (p.2.length + 1)).isSuffixOf p.1)
  exact PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && b)
    (fun p : List Bool × List Bool => decide (p.2.length + 1 < p.1.length))
    (fun p : List Bool × List Bool => (p.1.take (p.2.length + 1)).isSuffixOf p.1)
    guard_poly suffix_poly

/-- The decider: some `i` below `|x| + 1` makes the test pass. -/
private def borderDec (x : List Bool) : Bool :=
  (List.range (x.length + 1)).any (fun i => testV (x, List.replicate i true))

private theorem cpt_borderDec :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer borderDec := by
  show PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
    (fun x : List Bool => (List.range (x.length + 1)).any
      (fun i => testV (x, List.replicate i true)))
  exact PvsNP.Units.m2_bounded_unary_search_polytime testV cpt_testV

private theorem isSuffixOf_eq_true {a b : List Bool} :
    a.isSuffixOf b = true ↔ a <:+ b := by
  simp [List.isSuffixOf]

theorem border_in_p_main :
    ({x : List Bool | ∃ y : List Bool, y ≠ [] ∧ y.length < x.length ∧ y <+: x ∧ y <:+ x} :
      Language Bool) ∈ PvsNP.P := by
  refine ⟨borderDec, cpt_borderDec, fun x => ?_⟩
  show (∃ y : List Bool, y ≠ [] ∧ y.length < x.length ∧ y <+: x ∧ y <:+ x) ↔
    borderDec x = true
  constructor
  · rintro ⟨y, hyne, hylen, hypre, hysuf⟩
    have hypos : 0 < y.length := by
      cases y with
      | nil => exact (hyne rfl).elim
      | cons a t => simp
    have hi : y.length - 1 < x.length + 1 := by omega
    show (List.range (x.length + 1)).any (fun i => testV (x, List.replicate i true)) = true
    rw [List.any_eq_true]
    refine ⟨y.length - 1, List.mem_range.mpr hi, ?_⟩
    show testV (x, List.replicate (y.length - 1) true) = true
    show decide ((List.replicate (y.length - 1) true).length + 1 < x.length) &&
        (x.take ((List.replicate (y.length - 1) true).length + 1)).isSuffixOf x = true
    have hrep : (List.replicate (y.length - 1) true).length = y.length - 1 :=
      List.length_replicate
    rw [hrep]
    have h1 : y.length - 1 + 1 = y.length := by omega
    rw [h1]
    have htake : x.take y.length = y := (List.prefix_iff_eq_take.mp hypre).symm
    rw [htake]
    simp only [Bool.and_eq_true, decide_eq_true_eq, isSuffixOf_eq_true]
    exact ⟨hylen, hysuf⟩
  · intro h
    change (List.range (x.length + 1)).any
      (fun i => testV (x, List.replicate i true)) = true at h
    rw [List.any_eq_true] at h
    obtain ⟨i, hi, ht⟩ := h
    rw [List.mem_range] at hi
    have hrep : (List.replicate i true).length = i := List.length_replicate
    have ht2 : decide ((List.replicate i true).length + 1 < x.length) &&
        (x.take ((List.replicate i true).length + 1)).isSuffixOf x = true := ht
    rw [hrep] at ht2
    simp only [Bool.and_eq_true, decide_eq_true_eq, isSuffixOf_eq_true] at ht2
    obtain ⟨hguard, hsuf⟩ := ht2
    refine ⟨x.take (i + 1), ?_, ?_, ?_, ?_⟩
    · have hlen : (x.take (i + 1)).length = i + 1 := by
        rw [List.length_take]
        omega
      intro hnil
      rw [hnil, List.length_nil] at hlen
      omega
    · rw [List.length_take]
      omega
    · exact List.take_prefix (i + 1) x
    · exact hsuf

end PvsNP.Units.tl_lang_border_p

/-- The strings with a border are in P (TM2). -/
theorem PvsNP.Units.tl_lang_border_p :
    ({x : List Bool | ∃ y : List Bool, y ≠ [] ∧ y.length < x.length ∧ y <+: x ∧ y <:+ x} :
      Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_border_p.border_in_p_main
