import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_bounded_unary_search_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_count_witnesses

open PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library
open PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library.Machines
open PvsNP.Units.m2_bounded_unary_search_polytime.PEqualNP.Library.Universal

theorem cw_cptp {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

/-- `[true]` when the test accepts the pair, `[]` otherwise. -/
def cwFlag (f : List Bool × List Bool → Bool) (a b : List Bool) : List Bool :=
  if f (a, b) then [true] else []

def cT (s : List Bool) : List Bool := (unpairB s).1
def cX (s : List Bool) : List Bool := (unpairB (unpairB s).2).1
def cU (s : List Bool) : List Bool := (unpairB (unpairB s).2).2

/-- One step: add one to the tally when the test accepts the current count; count one more. -/
def cwStep (V : List Bool × List Bool → Bool) (s : List Bool) : List Bool :=
  pairB (cT s ++ cwFlag V (cX s) (cU s)) (pairB (cX s) ([true] ++ cU s))

theorem cwStep_eq (V : List Bool × List Bool → Bool) (acc x u : List Bool) :
    cwStep V (pairB acc (pairB x u)) =
      pairB (acc ++ cwFlag V x u) (pairB x (true :: u)) := by
  simp only [cwStep, cT, cX, cU, unpairB_pairB, List.singleton_append]

theorem cwFlag_len (V : List Bool × List Bool → Bool) (a b : List Bool) :
    (cwFlag V a b).length ≤ 1 := by
  unfold cwFlag; split <;> simp

theorem cwStep_len (V : List Bool × List Bool → Bool) (s : List Bool) :
    (cwStep V s).length ≤ s.length + 5 := by
  have a1 : 2 * (cT s).length + (unpairB s).2.length ≤ s.length := bs_unpairB_len s
  have a2 : 2 * (cX s).length + (cU s).length ≤ (unpairB s).2.length :=
    bs_unpairB_len (unpairB s).2
  have a3 := cwFlag_len V (cX s) (cU s)
  simp only [cwStep, pairB_length, List.length_append, List.length_singleton]
  omega

theorem cwFlag_eq (V : List Bool × List Bool → Bool) (x u : List Bool) :
    cwFlag V x u = List.replicate (if V (x, u) then 1 else 0) true := by
  unfold cwFlag; cases V (x, u) <;> rfl

theorem cwIter (V : List Bool × List Bool → Bool) (x : List Bool) : ∀ (k m : ℕ) (acc : List Bool),
    (unpairB ((cwStep V)^[k] (pairB acc (pairB x (List.replicate m true))))).1 =
      acc ++ List.replicate
        ((List.range k).countP (fun i => V (x, List.replicate (m + i) true))) true := by
  intro k
  induction k with
  | zero =>
    intro m acc
    simp [unpairB_pairB]
  | succ k ih =>
    intro m acc
    rw [Function.iterate_succ_apply, cwStep_eq, ← List.replicate_succ, ih, List.append_assoc,
      cwFlag_eq, List.replicate_append_replicate, List.range_succ_eq_map, List.countP_cons,
      List.countP_map]
    congr 2
    have e : ((fun i => V (x, List.replicate (m + 1 + i) true)) : ℕ → Bool) =
        (fun i => V (x, List.replicate (m + i) true)) ∘ Nat.succ := by
      funext i; simp only [Function.comp]; congr 3; omega
    rw [← e]
    simp only [Nat.add_zero]
    cases V (x, List.replicate m true) <;> simp [Nat.add_comm]

def cwF (V : List Bool × List Bool → Bool) (x : List Bool) : List Bool :=
  (unpairB ((cwStep V)^[x.length + 1] (pairB [] (pairB x [])))).1

theorem cwF_eq (V : List Bool × List Bool → Bool) (x : List Bool) :
    cwF V x = List.replicate
      ((List.range (x.length + 1)).countP (fun i => V (x, List.replicate i true))) true := by
  have h := cwIter V x (x.length + 1) 0 []
  simp only [List.replicate_zero, Nat.zero_add, List.nil_append] at h
  exact h

theorem cpt_cwF (V : List Bool × List Bool → Bool)
    (c : ComputableInPolyTime encodePair Computability.encodeBool V) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (cwF V) := by
  have hA : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cT :=
    cw_cptp cpt_unpairB1 (fun _ => rfl)
  have hR : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB s).2) := cpt_unpairB2
  have hX : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cX :=
    cw_cptp (cpt_comp hR cpt_unpairB1) (fun _ => rfl)
  have hU : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) cU :=
    cw_cptp (cpt_comp hR cpt_unpairB2) (fun _ => rfl)
  have hF : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => cwFlag V (cX s) (cU s)) :=
    cw_cptp (cpt_bitFlag (cpt_comp (cpt_pair hX hU) c)) (fun _ => rfl)
  have hA' := cpt_app2 hA hF
  have hU' := cpt_app2 (cpt_const [true]) hU
  have hg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (cwStep V) :=
    cw_cptp (cpt_pairB2 hA' (cpt_pairB2 hX hU')) (fun _ => rfl)
  have hI := cpt_iterB (cwStep V) hg (fun _ => 5) 5 (fun _ => le_refl 5)
    (cwStep_len V) (fun _ => by omega)
  have hs0 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => pairB [] (pairB x [])) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 cpt_id (cpt_const []))
  have hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x ++ [true]) :=
    cpt_app2 cpt_id (cpt_const [true])
  have hit := cpt_comp (cpt_pairB2 hs0 hcnt) hI
  have hres := cpt_comp hit cpt_unpairB1
  exact cw_cptp hres (fun x => by
    simp only [unpairB_pairB, cwF, List.length_append, List.length_singleton])

theorem count_polytime (V : List Bool × List Bool → Bool)
    (hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate
        ((List.range (x.length + 1)).countP (fun i => V (x, List.replicate i true))) true) := by
  have c : ComputableInPolyTime encodePair Computability.encodeBool V := hV
  have h := cpt_cwF V c
  have e : cwF V = fun x : List Bool => List.replicate
      ((List.range (x.length + 1)).countP (fun i => V (x, List.replicate i true))) true :=
    funext (cwF_eq V)
  rw [e] at h
  exact h

end PvsNP.Units.m2_tm_count_witnesses

theorem PvsNP.Units.m2_tm_count_witnesses :
    ∀ V : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V →
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => List.replicate ((List.range (x.length + 1)).countP (fun i => V (x, List.replicate i true))) true) :=
  PvsNP.Units.m2_tm_count_witnesses.count_polytime
