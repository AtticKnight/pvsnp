import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_tm_iterate_measure

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_y_inversions_unary

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def isHeadTrue : List Bool → List Bool
  | true :: _ => [true]
  | _ => []

def isHeadTrueδ : Bool → Bool → Bool × Option Bool
  | false, true => (true, some true)
  | false, false => (true, none)
  | true, _ => (true, none)

def isHeadTrueFin : Bool → Option Bool := fun _ => none

theorem isHeadTrue_run_true (x : List Bool) : fstRun isHeadTrueδ isHeadTrueFin true x = [] := by
  induction x with
  | nil => rfl
  | cons _ t ih => simp [fstRun, isHeadTrueδ, ih]

theorem isHeadTrue_run_false (x : List Bool) :
    fstRun isHeadTrueδ isHeadTrueFin false x = isHeadTrue x := by
  cases x with
  | nil => rfl
  | cons b t =>
    cases b <;> simp [fstRun, isHeadTrueδ, isHeadTrue_run_true, isHeadTrue]

theorem cpt_isHeadTrue :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) isHeadTrue :=
  fst_polyTime (fun x : List Bool => x) (fun x : List Bool => x) isHeadTrue
    isHeadTrueδ isHeadTrueFin false (fun x => (isHeadTrue_run_false x).symm)

def step (s : List Bool) : List Bool :=
  let r := (unpairB s).1
  let r2 := (unpairB s).2
  let c := (unpairB r2).1
  let t := (unpairB r2).2
  sel r (pairB [] (pairB c t))
    (sel (isHeadTrue r) (pairB r.tail (pairB c (c ++ t)))
      (pairB r.tail (pairB (true :: c) t)))

theorem cpt_step :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) step := by
  have hr := cpt_unpairB1
  have hr2 := cpt_unpairB2
  have hc := cpt_unpairB1_1 hr2
  have ht := cpt_unpairB2_1 hr2
  have hrt := cpt_tail1 hr
  have hnil := cpt_pairB2 (cpt_const []) (cpt_pairB2 hc ht)
  have hfalse := cpt_pairB2 hrt (cpt_pairB2 hc (cpt_app2 hc ht))
  have htrue := cpt_pairB2 hrt (cpt_pairB2 (cpt_cons1 true hc) ht)
  exact cpt_sel hr hnil (cpt_sel (cpt_comp hr cpt_isHeadTrue) hfalse htrue)

def meas (s : List Bool) : ℕ :=
  (unpairB s).1.length + (unpairB (unpairB s).2).1.length + 4

theorem meas_step (s : List Bool) : meas (step s) ≤ meas s := by
  dsimp only [meas, step]
  cases hr : (unpairB s).1 with
  | nil =>
    simp [sel, unpairB_pairB]
  | cons b r' =>
    cases b with
    | false =>
      simp [sel, isHeadTrue, unpairB_pairB]
    | true =>
      simp [sel, isHeadTrue, unpairB_pairB]
      omega

theorem len_step (s : List Bool) : (step s).length ≤ s.length + meas s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  dsimp only [meas, step]
  cases hr : (unpairB s).1 with
  | nil =>
    simp only [sel, ↓reduceIte, pairB_length, List.length_nil]
    rw [hr] at h1
    simp only [List.length_nil] at h1
    omega
  | cons b r' =>
    rw [hr] at h1
    cases b with
    | false =>
      simp only [sel, List.cons_ne_nil, ↓reduceIte, isHeadTrue, List.tail_cons, pairB_length,
        List.length_append, List.length_cons] at h1 ⊢
      omega
    | true =>
      simp only [sel, List.cons_ne_nil, ↓reduceIte, isHeadTrue, List.tail_cons, pairB_length,
        List.length_cons] at h1 ⊢
      omega

theorem meas_bound (s : List Bool) : meas s ≤ 4 * s.length + 4 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  dsimp only [meas]
  omega

def invCount (k : ℕ) : List Bool → ℕ
  | [] => 0
  | true :: r => invCount (k + 1) r
  | false :: r => k + invCount k r

theorem iter_step : ∀ (r : List Bool) (k m : ℕ),
    step^[r.length] (pairB r (pairB (List.replicate k true) (List.replicate m true))) =
      pairB [] (pairB (List.replicate (k + r.count true) true)
        (List.replicate (invCount k r + m) true)) := by
  intro r
  induction r with
  | nil =>
    intro k m
    simp [invCount]
  | cons b r' ih =>
    intro k m
    rw [List.length_cons, Function.iterate_succ_apply]
    cases b with
    | true =>
      have hst : step (pairB (true :: r') (pairB (List.replicate k true) (List.replicate m true))) =
          pairB r' (pairB (List.replicate (k + 1) true) (List.replicate m true)) := by
        simp [step, unpairB_pairB, sel, isHeadTrue, List.replicate_succ]
      rw [hst, ih (k + 1) m]
      have hc : (true :: r').count true = r'.count true + 1 := by simp
      rw [hc, invCount]
      have hadd : k + 1 + r'.count true = k + (r'.count true + 1) := by omega
      rw [hadd]
    | false =>
      have hst : step (pairB (false :: r') (pairB (List.replicate k true) (List.replicate m true))) =
          pairB r' (pairB (List.replicate k true) (List.replicate (k + m) true)) := by
        simp [step, unpairB_pairB, sel, isHeadTrue]
      rw [hst, ih k (k + m)]
      have hc : (false :: r').count true = r'.count true := by simp
      rw [hc, invCount]
      have hadd : invCount k r' + (k + m) = k + invCount k r' + m := by omega
      rw [hadd]

theorem invCount_eq : ∀ (r : List Bool) (k : ℕ),
    invCount k r =
      ((List.range r.length).map
        (fun j => if r.getD j false = true then 0 else k + (r.take j).count true)).sum := by
  intro r
  induction r with
  | nil =>
    intro k
    simp [invCount]
  | cons b r' ih =>
    intro k
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    cases b with
    | true =>
      simp only [invCount, List.getD_cons_zero, ↓reduceIte, zero_add]
      rw [ih (k + 1)]
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply, List.getD_cons_succ, List.take_succ_cons, List.count_cons,
        beq_self_eq_true, ↓reduceIte]
      have hadd : k + 1 + (r'.take j).count true = k + ((r'.take j).count true + 1) := by omega
      split_ifs
      · rfl
      · exact hadd
    | false =>
      simp only [invCount, List.getD_cons_zero, Bool.false_eq_true, ↓reduceIte, List.take_zero,
        List.count_nil, add_zero]
      rw [ih k]
      rfl

theorem main :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool =>
        List.replicate ((List.range x.length).map
          (fun j => if x.getD j false = true then 0 else (x.take j).count true)).sum true) := by
  have hIter : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => step^[p.2.length] p.1) :=
    PvsNP.Units.m2_tm_iterate_measure step meas 4 cpt_step meas_step len_step meas_bound
  have hInit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => pairB x (pairB [] [])) :=
    cpt_pairB2 cpt_id (cpt_const (pairB [] []))
  have hPair : ComputableInPolyTime (fun x : List Bool => x) encodePair
      (fun x : List Bool => (pairB x (pairB [] []), x)) :=
    cpt_pair hInit cpt_id
  have hRun : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => step^[x.length] (pairB x (pairB [] []))) :=
    cpt_comp hPair hIter
  have hOut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => (unpairB (unpairB (step^[x.length] (pairB x (pairB [] [])))).2).2) :=
    cpt_unpairB2_1 (cpt_unpairB2_1 hRun)
  have heq : (fun x : List Bool =>
      (unpairB (unpairB (step^[x.length] (pairB x (pairB [] [])))).2).2) =
      (fun x : List Bool =>
        List.replicate ((List.range x.length).map
          (fun j => if x.getD j false = true then 0 else (x.take j).count true)).sum true) := by
    funext x
    have h1 := iter_step x 0 0
    simp only [List.replicate_zero, add_zero] at h1
    rw [h1, unpairB_pairB, unpairB_pairB, invCount_eq x 0]
    simp
  rw [← heq]
  exact hOut

end PvsNP.Units.m2_tm_y_inversions_unary

theorem PvsNP.Units.m2_tm_y_inversions_unary :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool =>
        List.replicate ((List.range x.length).map
          (fun j => if x.getD j false = true then 0 else (x.take j).count true)).sum true) :=
  PvsNP.Units.m2_tm_y_inversions_unary.main
