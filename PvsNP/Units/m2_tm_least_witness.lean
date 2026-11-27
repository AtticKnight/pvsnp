import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_bounded_unary_search_polytime

/-
Built on the settled unit PvsNP.Units.m2_bounded_unary_search_polytime of github.com/makedotfun/pvsnp
(its copied library: pairB/unpairB, sel, cpt_sel, cpt_app2, cpt_pairB2, cpt_bitFlag, cpt_iterB and the
search step bsStep). Here |x| + 1 steps of that search step are run with one more counter, which grows
by one at every step while the flag is still unset, so it ends as the least witness count in unary.
-/

namespace PvsNP.Units.m2_tm_least_witness

open PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library
open PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library.Machines
open PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library.Universal

theorem cptp {f f' : List Bool → List Bool}
    (h : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f)
    (e : ∀ a, f a = f' a) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- The count of leading rejected counts among `m, m + 1, ..., m + k - 1`. -/
def cnt (V : List Bool × List Bool → Bool) (x : List Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, m => if V (x, List.replicate m true) then 0 else cnt V x k (m + 1) + 1

theorem cnt_eq (V : List Bool × List Bool → Bool) (x : List Bool) : ∀ k m : ℕ,
    cnt V x k m = ((List.range' m k).takeWhile (fun i => !V (x, List.replicate i true))).length := by
  intro k
  induction k with
  | zero => intro m; simp [cnt]
  | succ k ih =>
    intro m
    cases h : V (x, List.replicate m true)
    · first
        | simp [cnt, h, ih, List.range'_succ, List.takeWhile_cons]
        | simp [cnt, h, ih, List.range', List.takeWhile]
    · first
        | simp [cnt, h, List.range'_succ, List.takeWhile_cons]
        | simp [cnt, h, List.range', List.takeWhile]

/-- One step: the search step on the inner state, and one more count while the new flag is unset. -/
def lwStep (V : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  pairB (sel (bA (bsStep V (unpairB s).2)) [true] [] ++ (unpairB s).1) (bsStep V (unpairB s).2)

theorem lwStep_eq (V : List Bool × List Bool → Bool) (c acc x u : List Bool) :
    lwStep V (pairB c (pairB acc (pairB x u))) =
      pairB (sel (sel (bsFlag V x u) acc [true]) [true] [] ++ c)
        (pairB (sel (bsFlag V x u) acc [true]) (pairB x (true :: u))) := by
  simp only [lwStep, unpairB_pairB, bsStep_eq, bA]

theorem sel_of_ne (f a b : List Bool) (h : f ≠ []) : sel f a b = b := by
  unfold sel
  exact if_neg h

theorem sel_ne (f acc : List Bool) (h : acc ≠ []) : sel f acc [true] ≠ [] := by
  unfold sel
  split
  · exact h
  · simp

theorem lw_done (V : List Bool × List Bool → Bool) (x : List Bool) : ∀ (k : ℕ) (c acc u : List Bool),
    acc ≠ [] → (unpairB ((lwStep V)^[k] (pairB c (pairB acc (pairB x u))))).1 = c := by
  intro k
  induction k with
  | zero => intro c acc u _; simp only [Function.iterate_zero, id_eq, unpairB_pairB]
  | succ k ih =>
    intro c acc u h
    rw [Function.iterate_succ_apply, lwStep_eq]
    have h2 := sel_ne (bsFlag V x u) acc h
    rw [ih _ _ _ h2, sel_of_ne _ _ _ h2, List.nil_append]

theorem lw_run (V : List Bool × List Bool → Bool) (x : List Bool) : ∀ (k m a : ℕ),
    (unpairB ((lwStep V)^[k] (pairB (List.replicate a true)
      (pairB [] (pairB x (List.replicate m true)))))).1 = List.replicate (a + cnt V x k m) true := by
  intro k
  induction k with
  | zero => intro m a; simp only [Function.iterate_zero, id_eq, unpairB_pairB, cnt, Nat.add_zero]
  | succ k ih =>
    intro m a
    rw [Function.iterate_succ_apply, lwStep_eq]
    cases h : V (x, List.replicate m true)
    · have e1 : sel (bsFlag V x (List.replicate m true)) [] [true] = [] := by
        simp [sel, bsFlag, h]
      have e2 : sel ([] : List Bool) [true] [] ++ List.replicate a true = List.replicate (a + 1) true := by
        simp [sel, List.replicate_succ]
      rw [e1, e2, ← List.replicate_succ, ih]
      congr 1
      rw [show cnt V x (k + 1) m = cnt V x k (m + 1) + 1 by simp [cnt, h]]
      omega
    · have e1 : sel (bsFlag V x (List.replicate m true)) [] [true] = [true] := by
        simp [sel, bsFlag, h]
      rw [e1, lw_done V x k _ [true] _ (by simp)]
      simp [sel, cnt, h]

theorem lwStep_len (V : List Bool × List Bool → Bool) (s : List Bool) :
    (lwStep V s).length ≤ s.length + 8 := by
  have a1 := bs_unpairB_len s
  have a2 := bsStep_len V (unpairB s).2
  have a3 : (sel (bA (bsStep V (unpairB s).2)) [true] []).length ≤ 1 := by
    unfold sel; split <;> simp
  simp only [lwStep, pairB_length, List.length_append]
  omega

theorem cpt_bsStep (V : List Bool × List Bool → Bool)
    (c : ComputableInPolyTime PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library.encodePair
      Computability.encodeBool V) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (bsStep V) := by
  have hA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) bA :=
    cptp cpt_unpairB1 (fun _ => rfl)
  have hR : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hX : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) bX :=
    cptp (cpt_comp hR cpt_unpairB1) (fun _ => rfl)
  have hU : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) bU :=
    cptp (cpt_comp hR cpt_unpairB2) (fun _ => rfl)
  have hF : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => bsFlag V (bX s) (bU s)) :=
    cptp (cpt_bitFlag (cpt_comp (cpt_pair hX hU) c)) (fun _ => rfl)
  have hA' := cpt_sel hF hA (cpt_const [true])
  have hU' := cpt_app2 (cpt_const [true]) hU
  exact cptp (cpt_pairB2 hA' (cpt_pairB2 hX hU')) (fun _ => rfl)

theorem cpt_lwStep (V : List Bool × List Bool → Bool)
    (c : ComputableInPolyTime PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library.encodePair
      Computability.encodeBool V) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (lwStep V) := by
  have hB := cpt_bsStep V c
  have hI : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => bsStep V (unpairB s).2) := cpt_comp cpt_unpairB2 hB
  have hA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => bA (bsStep V (unpairB s).2)) := cptp (cpt_comp hI cpt_unpairB1) (fun _ => rfl)
  have hS := cpt_sel hA (cpt_const [true]) (cpt_const [])
  have hC := cpt_app2 hS cpt_unpairB1
  exact cptp (cpt_pairB2 hC hI) (fun _ => rfl)

/-- The least witness count, as the counter after `|x| + 1` steps. -/
def lwF (V : List Bool × List Bool → Bool) (x : List Bool) : List Bool :=
  (unpairB ((lwStep V)^[x.length + 1] (pairB [] (pairB [] (pairB x []))))).1

theorem lwF_eq (V : List Bool × List Bool → Bool) (x : List Bool) :
    lwF V x = List.replicate ((List.range (x.length + 1)).takeWhile
      (fun i => !V (x, List.replicate i true))).length true := by
  have h := lw_run V x (x.length + 1) 0 0
  simp only [List.replicate_zero, Nat.zero_add] at h
  rw [lwF, h, cnt_eq]
  first
    | rw [List.range_eq_range']
    | simp [List.range_eq_range']

theorem cpt_lwF (V : List Bool × List Bool → Bool)
    (c : ComputableInPolyTime PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library.encodePair
      Computability.encodeBool V) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (lwF V) := by
  have hI := cpt_iterB (lwStep V) (cpt_lwStep V c) (fun _ => 8) 8 (fun _ => le_refl 8)
    (lwStep_len V) (fun _ => by omega)
  have hs0 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => pairB [] (pairB [] (pairB x []))) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_id (cpt_const [])))
  have hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x ++ [true]) :=
    cpt_app2 cpt_id (cpt_const [true])
  have hit := cpt_comp (cpt_pairB2 hs0 hcnt) hI
  have hres := cpt_comp hit cpt_unpairB1
  exact cptp hres (fun x => by
    simp only [unpairB_pairB, lwF, List.length_append, List.length_singleton])

theorem main (V : List Bool × List Bool → Bool)
    (hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate ((List.range (x.length + 1)).takeWhile
        (fun i => !V (x, List.replicate i true))).length true) := by
  have c : ComputableInPolyTime PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library.encodePair
      Computability.encodeBool V := hV
  have h := cpt_lwF V c
  have e : lwF V = fun x : List Bool => List.replicate ((List.range (x.length + 1)).takeWhile
      (fun i => !V (x, List.replicate i true))).length true :=
    funext (lwF_eq V)
  rw [e] at h
  exact h

end PvsNP.Units.m2_tm_least_witness

/-- The least unary witness up to the input length, in unary, takes polynomial time (TM2). -/
theorem PvsNP.Units.m2_tm_least_witness :
    ∀ V : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V →
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => List.replicate ((List.range (x.length + 1)).takeWhile (fun i => !V (x, List.replicate i true))).length true) :=
  PvsNP.Units.m2_tm_least_witness.main
