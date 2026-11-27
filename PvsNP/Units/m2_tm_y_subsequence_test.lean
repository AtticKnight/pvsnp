import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_tm_y_subsequence_test

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem encodePair_eq : PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
  funext ⟨x, y⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

def headδ : Bool → Bool → Bool × Option Bool
  | false, b => (true, some b)
  | true, _ => (true, none)

def headFin : Bool → Option Bool
  | false => some false
  | true => none

theorem headδ_true (r : List Bool) : fstRun headδ headFin true r = [] := by
  induction r with
  | nil => rfl
  | cons _ t ih => simp [fstRun, headδ, ih]

theorem headδ_false (r : List Bool) :
    fstRun headδ headFin false r = Computability.encodeBool (r.headD false) := by
  cases r with
  | nil => rfl
  | cons b t => simp [fstRun, headδ, headδ_true, Computability.encodeBool]

theorem cpt_headFlag :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun l : List Bool => if l.headD false then [true] else []) :=
  cpt_bitFlag (fst_polyTime _ _ _ headδ headFin false (fun r => (headδ_false r).symm))

def isEmptyδ : Bool → Bool → Bool × Option Bool
  | _, _ => (false, none)

def isEmptyFin : Bool → Option Bool
  | true => some true
  | false => some false

theorem isEmpty_false (r : List Bool) : fstRun isEmptyδ isEmptyFin false r = [false] := by
  induction r with
  | nil => rfl
  | cons _ t ih => simp [fstRun, isEmptyδ, ih]

theorem isEmpty_true (r : List Bool) :
    fstRun isEmptyδ isEmptyFin true r = Computability.encodeBool (decide (r = [])) := by
  cases r with
  | nil => rfl
  | cons _ t => simp [fstRun, isEmptyδ, isEmpty_false, Computability.encodeBool]

theorem cpt_isEmpty :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => decide (l = [])) :=
  fst_polyTime _ _ _ isEmptyδ isEmptyFin true (fun r => (isEmpty_true r).symm)

def subStep (s : List Bool) : List Bool :=
  let u := (unpairB s).1
  let v := (unpairB s).2
  sel u s
    (sel v s
      (sel (if u.headD false then [true] else [])
        (sel (if v.headD false then [true] else []) (pairB u.tail v.tail) (pairB u v.tail))
        (sel (if v.headD false then [true] else []) (pairB u v.tail) (pairB u.tail v.tail))))

theorem subStep_len_le (s : List Bool) : (subStep s).length ≤ s.length + 1 := by
  have h0 := unpairB_length s
  have htu : (unpairB s).1.tail.length ≤ (unpairB s).1.length := by
    cases (unpairB s).1 <;> simp
  have htv : (unpairB s).2.tail.length ≤ (unpairB s).2.length := by
    cases (unpairB s).2 <;> simp
  unfold subStep sel
  dsimp only
  split_ifs <;> (try simp only [pairB_length]) <;> omega

theorem cpt_subStep :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) subStep := by
  have hu := cpt_unpairB1
  have hv := cpt_unpairB2
  have hhu := cpt_comp (f := fun s => (unpairB s).1)
    (g := fun l : List Bool => if l.headD false then [true] else []) hu cpt_headFlag
  have hhv := cpt_comp (f := fun s => (unpairB s).2)
    (g := fun l : List Bool => if l.headD false then [true] else []) hv cpt_headFlag
  have hMatch := cpt_pairB2 (cpt_tail1 hu) (cpt_tail1 hv)
  have hSkip := cpt_pairB2 hu (cpt_tail1 hv)
  exact cpt_sel hu cpt_id
    (cpt_sel hv cpt_id
      (cpt_sel hhu (cpt_sel hhv hMatch hSkip) (cpt_sel hhv hSkip hMatch)))

theorem subStep_nil_fix (k : ℕ) (v : List Bool) :
    subStep^[k] (pairB [] v) = pairB [] v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    have h1 : subStep (pairB [] v) = pairB [] v := by
      unfold subStep sel
      simp [unpairB_pairB]
    rw [h1, ih]

theorem subStep_iter_iff (v : List Bool) :
    ∀ u : List Bool,
      (unpairB (subStep^[v.length] (pairB u v))).1 = [] ↔ List.Sublist u v := by
  induction v with
  | nil =>
    intro u
    simp [unpairB_pairB]
  | cons b vt ih =>
    intro u
    cases u with
    | nil =>
      rw [subStep_nil_fix, unpairB_pairB]
      simp
    | cons a ut =>
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply]
      by_cases hab : a = b
      · subst hab
        have hstep : subStep (pairB (a :: ut) (a :: vt)) = pairB ut vt := by
          unfold subStep sel
          simp only [unpairB_pairB]
          cases a <;> simp
        rw [hstep, ih ut]
        exact List.cons_sublist_cons.symm
      · have hstep : subStep (pairB (a :: ut) (b :: vt)) = pairB (a :: ut) vt := by
          unfold subStep sel
          simp only [unpairB_pairB]
          cases a <;> cases b <;> simp at hab ⊢
        rw [hstep, ih (a :: ut)]
        constructor
        · intro h
          exact h.trans (List.sublist_cons_self b vt)
        · intro h
          cases h with
          | cons _ h' => exact h'
          | cons_cons _ _ => exact absurd rfl hab

def subStr (s : List Bool) : Bool :=
  decide ((unpairB (subStep^[(unpairB s).2.length] s)).1 = [])

def subFun (p : List Bool × List Bool) : Bool :=
  subStr (pairB p.1 p.2)

theorem subFun_eq (p : List Bool × List Bool) :
    subFun p = decide (List.Sublist p.1 p.2) := by
  unfold subFun subStr
  simp only [unpairB_pairB]
  by_cases h : List.Sublist p.1 p.2
  · have h1 := (subStep_iter_iff p.2 p.1).2 h
    simp [h, h1]
  · have h1 : (unpairB (subStep^[p.2.length] (pairB p.1 p.2))).1 ≠ [] :=
      fun he => h ((subStep_iter_iff p.2 p.1).1 he)
    simp [h, h1]

theorem subsequence_test_aux :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (List.Sublist p.1 p.2)) := by
  have hiter := cpt_iterGrow cpt_subStep 1 subStep_len_le cpt_unpairB2 cpt_id
  have hstr : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool subStr :=
    cpt_comp (f := fun s => (unpairB (subStep^[(unpairB s).2.length] s)).1)
      (g := fun l => decide (l = [])) (cpt_unpairB1_1 hiter) cpt_isEmpty
  have hpair : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool subFun :=
    cpt_comp (f := fun p : List Bool × List Bool => pairB p.1 p.2) (g := subStr) cpt_pairB hstr
  have hfun : subFun = fun p : List Bool × List Bool => decide (List.Sublist p.1 p.2) :=
    funext subFun_eq
  rw [hfun] at hpair
  rw [encodePair_eq]
  exact hpair

end PvsNP.Units.m2_tm_y_subsequence_test

/-- Deciding whether the first binary string is a subsequence of the second takes polynomial time (TM2). -/
theorem PvsNP.Units.m2_tm_y_subsequence_test :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (List.Sublist p.1 p.2)) :=
  PvsNP.Units.m2_tm_y_subsequence_test.subsequence_test_aux
