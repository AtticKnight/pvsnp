import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_bounded_unary_search_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_y_prefix_counts_list

open PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library
open PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library.Machines
open PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library.Universal

private theorem pc_cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- Returns `[true]` if the list starts with `true`, otherwise `[]`. -/
def headTrue : List Bool → List Bool
  | true :: _ => [true]
  | _ => []

private def htD : Bool → Bool → Bool × Option Bool
  | false, true => (true, some true)
  | false, false => (true, none)
  | true, _ => (true, none)

private theorem htD_true (l : List Bool) :
    fstRun htD (fun _ => none) true l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, htD, ih]

private theorem htD_false (l : List Bool) :
    fstRun htD (fun _ => none) false l = headTrue l := by
  cases l with
  | nil => rfl
  | cons b l => cases b <;> simp [fstRun, htD, headTrue, htD_true]

theorem cpt_headTrue :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) headTrue :=
  fst_polyTime _ _ _ htD (fun _ => none) false (fun s => (htD_false s).symm)

theorem headTrue_len (l : List Bool) : (headTrue l).length ≤ 1 := by
  cases l with
  | nil => simp [headTrue]
  | cons b l => cases b <;> simp [headTrue]

def pcOut (s : List Bool) : List Bool := (unpairB s).1
def pcRem (s : List Bool) : List Bool := (unpairB (unpairB s).2).1
def pcCnt (s : List Bool) : List Bool := (unpairB (unpairB s).2).2

/-- One step: append `cnt ++ [false]` to `out`, pop a bit from `rem`, and increment `cnt` if `true`. -/
def pcStep (s : List Bool) : List Bool :=
  pairB (pcOut s ++ (pcCnt s ++ [false]))
    (pairB (pcRem s).tail (pcCnt s ++ headTrue (pcRem s)))

theorem pcStep_eq (out rem cnt : List Bool) :
    pcStep (pairB out (pairB rem cnt)) =
      pairB (out ++ (cnt ++ [false])) (pairB rem.tail (cnt ++ headTrue rem)) := by
  simp only [pcStep, pcOut, pcRem, pcCnt, unpairB_pairB]

def pcM (s : List Bool) : ℕ := 2 * ((pcRem s).length + (pcCnt s).length) + 7

theorem pcM_step (s : List Bool) : pcM (pcStep s) ≤ pcM s := by
  simp only [pcM, pcStep, pcRem, pcCnt, unpairB_pairB, List.length_append]
  cases h : (unpairB (unpairB s).2).1 with
  | nil => simp [headTrue]
  | cons b r =>
    cases b
    · simp [headTrue]
    · simp [headTrue]; omega

theorem pcStep_len (s : List Bool) : (pcStep s).length ≤ s.length + pcM s := by
  have a1 : 2 * (pcOut s).length + (unpairB s).2.length ≤ s.length := bs_unpairB_len s
  have a2 : 2 * (pcRem s).length + (pcCnt s).length ≤ (unpairB s).2.length :=
    bs_unpairB_len (unpairB s).2
  have a3 : (headTrue (pcRem s)).length ≤ 1 := headTrue_len (pcRem s)
  have a4 : (pcRem s).tail.length ≤ (pcRem s).length := by simp
  simp only [pcStep, pcM, pairB_length, List.length_append, List.length_singleton]
  omega

theorem pcM_bound (s : List Bool) : pcM s ≤ 7 * s.length + 7 := by
  have a1 : 2 * (pcOut s).length + (unpairB s).2.length ≤ s.length := bs_unpairB_len s
  have a2 : 2 * (pcRem s).length + (pcCnt s).length ≤ (unpairB s).2.length :=
    bs_unpairB_len (unpairB s).2
  simp only [pcM]
  omega

theorem pcIter : ∀ (b a out : List Bool),
    (unpairB (pcStep^[b.length + 1]
        (pairB out (pairB b (List.replicate (a.count true) true))))).1 =
      out ++ (List.range (b.length + 1)).flatMap
        (fun i => List.replicate ((a ++ b.take i).count true) true ++ [false]) := by
  intro b
  induction b with
  | nil =>
    intro a out
    simp [pcStep_eq, unpairB_pairB]
  | cons d bs ih =>
    intro a out
    rw [List.length_cons, Function.iterate_succ_apply, pcStep_eq]
    have hcnt : List.replicate (a.count true) true ++ headTrue (d :: bs) =
        List.replicate ((a ++ [d]).count true) true := by
      cases d <;> simp [headTrue, List.replicate_succ']
    rw [List.tail_cons, hcnt, ih (a ++ [d]) (out ++ (List.replicate (a.count true) true ++ [false]))]
    rw [List.append_assoc]
    conv_rhs => rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    congr 1
    congr 1
    · simp
    · apply List.flatMap_congr
      intro i _
      simp [List.append_assoc]

def pcF (x : List Bool) : List Bool :=
  (unpairB (pcStep^[x.length + 1] (pairB [] (pairB x [])))).1

theorem pcF_eq (x : List Bool) :
    pcF x = (List.range (x.length + 1)).flatMap
      (fun i => List.replicate ((x.take i).count true) true ++ [false]) := by
  have h := pcIter x [] []
  simpa [pcF] using h

theorem cpt_pcF :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pcF := by
  have hOut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pcOut :=
    pc_cptp cpt_unpairB1 (fun _ => rfl)
  have hR : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hRem : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pcRem :=
    pc_cptp (cpt_comp hR cpt_unpairB1) (fun _ => rfl)
  have hCnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pcCnt :=
    pc_cptp (cpt_comp hR cpt_unpairB2) (fun _ => rfl)
  have hOut' := cpt_app2 hOut (cpt_app2 hCnt (cpt_const [false]))
  have hRem' := cpt_comp hRem cpt_tail
  have hCnt' := cpt_app2 hCnt (cpt_comp hRem cpt_headTrue)
  have hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) pcStep :=
    pc_cptp (cpt_pairB2 hOut' (cpt_pairB2 hRem' hCnt')) (fun _ => rfl)
  have hI := cpt_iterB pcStep hg pcM 7 pcM_step pcStep_len pcM_bound
  have hs0 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => pairB [] (pairB x [])) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_id (cpt_const []))
  have hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x ++ [true]) :=
    cpt_app2 cpt_id (cpt_const [true])
  have hit := cpt_comp (cpt_pairB2 hs0 hcnt) hI
  have hres := cpt_comp hit cpt_unpairB1
  exact pc_cptp hres (fun x => by
    simp only [unpairB_pairB, pcF, List.length_append, List.length_singleton])

end PvsNP.Units.m2_tm_y_prefix_counts_list

theorem PvsNP.Units.m2_tm_y_prefix_counts_list :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => (List.range (x.length + 1)).flatMap
        (fun i => List.replicate ((x.take i).count true) true ++ [false])) := by
  have h := PvsNP.Units.m2_tm_y_prefix_counts_list.cpt_pcF
  have e : PvsNP.Units.m2_tm_y_prefix_counts_list.pcF =
      fun x : List Bool => (List.range (x.length + 1)).flatMap
        (fun i => List.replicate ((x.take i).count true) true ++ [false]) :=
    funext PvsNP.Units.m2_tm_y_prefix_counts_list.pcF_eq
  rw [e] at h
  exact h
