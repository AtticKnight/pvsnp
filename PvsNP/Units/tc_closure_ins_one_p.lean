import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp (Apache License
2.0), whose machine combinators come from github.com/open-goat/pequalnp-proofs (formerly
brilliant-hq/pequalnp-proofs) at commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License
2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_ins_one_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private def firstD : Bool → Bool → Bool × Option Bool
  | false, b => (true, some b)
  | true, _ => (true, none)

private theorem run_first_tail (l : List Bool) :
    fstRun firstD (fun _ => none) true l = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simpa [fstRun, firstD] using ih

private theorem run_first (x : List Bool) :
    x.take 1 = fstRun firstD (fun _ => none) false x := by
  cases x with
  | nil => rfl
  | cons _ _ => simp [fstRun, firstD, run_first_tail]

private theorem cpt_take1 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x.take 1) :=
  fst_polyTime (fun x : List Bool => x) (fun x : List Bool => x) _ firstD (fun _ => none)
    false run_first

private def headBit : List Bool → List Bool
  | true :: _ => [true]
  | _ => []

private def headBitD : Bool → Bool → Bool × Option Bool
  | false, true => (true, some true)
  | false, false => (true, none)
  | true, _ => (true, none)

private theorem run_headBit_tail (l : List Bool) :
    fstRun headBitD (fun _ => none) true l = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simpa [fstRun, headBitD] using ih

private theorem run_headBit (x : List Bool) :
    headBit x = fstRun headBitD (fun _ => none) false x := by
  cases x with
  | nil => rfl
  | cons b tl =>
    cases b <;> simp [headBit, fstRun, headBitD, run_headBit_tail]

private theorem cpt_headBit :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) headBit :=
  fst_polyTime (fun x : List Bool => x) (fun x : List Bool => x) _ headBitD (fun _ => none)
    false run_headBit

private def headOutFin : Bool → Option Bool
  | false => some false
  | true => none

private theorem run_headOut_tail (l : List Bool) :
    fstRun firstD headOutFin true l = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simpa [fstRun, firstD, headOutFin] using ih

private theorem run_headOut (x : List Bool) :
    [x.headD false] = fstRun firstD headOutFin false x := by
  cases x with
  | nil => rfl
  | cons _ _ => simp [fstRun, firstD, run_headOut_tail]

private theorem cpt_headOut :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => [x.headD false]) :=
  fst_polyTime (fun x : List Bool => x) (fun x : List Bool => x) _ firstD headOutFin
    false run_headOut

/-- The already-scanned prefix of the state `acc :: pairB u v`. -/
private def uOf (s : List Bool) : List Bool := (unpairB s.tail).1

/-- The not-yet-scanned suffix of the state `acc :: pairB u v`. -/
private def vOf (s : List Bool) : List Bool := (unpairB s.tail).2

/-- The candidate obtained by deleting the head of `vOf s`. -/
private def candOf (s : List Bool) : List Bool := uOf s ++ (vOf s).tail

private def flagCand (d : List Bool → Bool) (s : List Bool) : List Bool :=
  if d (candOf s) then [true] else []

/-- Nonempty iff the accumulator is already true, or `vOf s` is nonempty and the
current deletion candidate is accepted by `d`. -/
private def orFlag (d : List Bool → Bool) (s : List Bool) : List Bool :=
  sel (vOf s) (headBit s) (headBit s ++ flagCand d s)

/-- The pair after moving the head of `vOf s` onto the end of `uOf s`
(a no-op when `vOf s = []`). -/
private def newPair (s : List Bool) : List Bool :=
  pairB (uOf s ++ (vOf s).take 1) (vOf s).tail

private def step (d : List Bool → Bool) (s : List Bool) : List Bool :=
  sel s [] (sel (orFlag d s) (false :: newPair s) (true :: newPair s))

private theorem step_apply (d : List Bool → Bool) (acc : Bool) (u v : List Bool) :
    step d (acc :: pairB u v) =
      (acc || (!v.isEmpty && d (u ++ v.tail))) :: pairB (u ++ v.take 1) v.tail := by
  cases v with
  | nil =>
    cases acc <;> simp [step, orFlag, flagCand, candOf, newPair, uOf, vOf, headBit, sel,
      unpairB_pairB]
  | cons b v' =>
    cases acc <;> cases hd : d (u ++ v') <;>
      simp [step, orFlag, flagCand, candOf, newPair, uOf, vOf, headBit, sel, unpairB_pairB, hd]

private theorem take_one_length_le (v : List Bool) : (v.take 1).length ≤ 1 := by
  cases v <;> simp

private theorem tail_length_le (v : List Bool) : v.tail.length ≤ v.length := by
  cases v <;> simp

private theorem step_len (d : List Bool → Bool) (s : List Bool) :
    (step d s).length ≤ s.length + 3 := by
  cases s with
  | nil => simp [step, sel]
  | cons acc t =>
    have h1 := unpairB_length t
    have h2 := take_one_length_le (unpairB t).2
    have h3 := tail_length_le (unpairB t).2
    have hlen : (step d (acc :: t)).length = (newPair (acc :: t)).length + 1 := by
      by_cases h : orFlag d (acc :: t) = [] <;> simp [step, sel, h]
    rw [hlen]
    simp only [newPair, uOf, vOf, List.tail_cons, pairB_length, List.length_append,
      List.length_cons]
    omega

private theorem cpt_step {d : List Bool → Bool}
    (hd : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool d) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (step d) := by
  have hu : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => uOf s) :=
    cpt_unpairB1_1 (cpt_tail1 cpt_id)
  have hv : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => vOf s) :=
    cpt_unpairB2_1 (cpt_tail1 cpt_id)
  have htake1v : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (vOf s).take 1) :=
    cpt_comp hv cpt_take1
  have hu' : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => uOf s ++ (vOf s).take 1) :=
    cpt_app2 hu htake1v
  have hv' : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (vOf s).tail) :=
    cpt_tail1 hv
  have hnewPair : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => newPair s) :=
    cpt_pairB2 hu' hv'
  have hcand : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => candOf s) :=
    cpt_app2 hu hv'
  have hflag : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => flagCand d s) :=
    cpt_bitFlag (cpt_comp hcand hd)
  have hor : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => orFlag d s) :=
    cpt_sel hv cpt_headBit (cpt_app2 cpt_headBit hflag)
  have hinner : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool =>
        sel (orFlag d s) (false :: newPair s) (true :: newPair s)) :=
    cpt_sel hor (cpt_cons1 false hnewPair) (cpt_cons1 true hnewPair)
  exact cpt_sel cpt_id (cpt_const []) hinner

private theorem take_drop_succ (x : List Bool) (k : ℕ) :
    x.take (k + 1) = x.take k ++ (x.drop k).take 1 := by
  induction x generalizing k with
  | nil => simp
  | cons b t ih =>
    cases k with
    | zero => simp
    | succ k =>
      have h := ih k
      simp only [List.take_succ_cons, List.drop_succ_cons]
      rw [h]
      simp

private theorem drop_tail_succ (x : List Bool) (k : ℕ) :
    (x.drop k).tail = x.drop (k + 1) := by
  induction x generalizing k with
  | nil => simp
  | cons b t ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.drop_succ_cons]
      exact ih k

private def accOf (d : List Bool → Bool) (x : List Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => accOf d x k || (!(x.drop k).isEmpty && d (x.take k ++ (x.drop k).tail))

private theorem step_iter (d : List Bool → Bool) (x : List Bool) : ∀ k : ℕ,
    (step d)^[k] (false :: pairB [] x) = accOf d x k :: pairB (x.take k) (x.drop k)
  | 0 => by simp [accOf]
  | k + 1 => by
    have hpair : pairB (x.take k ++ (x.drop k).take 1) (x.drop k).tail =
        pairB (x.take (k + 1)) (x.drop (k + 1)) := by
      congr 1
      · exact (take_drop_succ x k).symm
      · exact drop_tail_succ x k
    rw [Function.iterate_succ_apply', step_iter d x k, step_apply, hpair]
    rfl

private theorem accOf_iff (d : List Bool → Bool) (x : List Bool) : ∀ k : ℕ,
    accOf d x k = true ↔
      ∃ i < k, ∃ b v', x.drop i = b :: v' ∧ d (x.take i ++ v') = true
  | 0 => by simp [accOf]
  | k + 1 => by
    have hcond : (!(x.drop k).isEmpty && d (x.take k ++ (x.drop k).tail)) = true ↔
        ∃ b v', x.drop k = b :: v' ∧ d (x.take k ++ v') = true := by
      cases hdrop : x.drop k with
      | nil => simp [hdrop]
      | cons b v' => simp [hdrop]
    show (accOf d x k || (!(x.drop k).isEmpty && d (x.take k ++ (x.drop k).tail))) = true ↔ _
    rw [Bool.or_eq_true, accOf_iff d x k, hcond]
    constructor
    · rintro (⟨i, hi, rest⟩ | ⟨b, v', hbv, hd⟩)
      · exact ⟨i, by omega, rest⟩
      · exact ⟨k, by omega, b, v', hbv, hd⟩
    · rintro ⟨i, hi, b, v', hbv, hd⟩
      by_cases hik : i < k
      · exact Or.inl ⟨i, hik, b, v', hbv, hd⟩
      · have hie : i = k := by omega
        subst hie
        exact Or.inr ⟨b, v', hbv, hd⟩

private def dec (d : List Bool → Bool) (x : List Bool) : Bool :=
  ((step d)^[x.length] (false :: pairB [] x)).headD false

private theorem dec_iff {L : Language Bool} {d : List Bool → Bool}
    (hdec : ∀ x, x ∈ L ↔ d x = true) (x : List Bool) :
    (∃ u v b, x = u ++ b :: v ∧ u ++ v ∈ L) ↔ dec d x = true := by
  have heq : dec d x = accOf d x x.length := by
    unfold dec
    rw [step_iter]
    rfl
  rw [heq, accOf_iff]
  constructor
  · rintro ⟨u, v, b, hx, hmem⟩
    have hlen : u.length < x.length := by
      rw [hx]
      simp only [List.length_append, List.length_cons]
      omega
    refine ⟨u.length, hlen, b, v, ?_, ?_⟩
    · rw [hx, List.drop_left]
    · have hduv : d (u ++ v) = true := (hdec (u ++ v)).mp hmem
      rw [hx, List.take_left]
      exact hduv
  · rintro ⟨i, _, b, v, hdrop, hdtrue⟩
    refine ⟨x.take i, v, b, ?_, ?_⟩
    · have h := List.take_append_drop i x
      rw [hdrop] at h
      exact h.symm
    · exact (hdec _).mpr hdtrue

private theorem closure_ins_one_p :
    ∀ L : Language Bool, L ∈ PvsNP.P →
      ({x : List Bool | ∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ v ∈ L} :
        Language Bool) ∈ PvsNP.P := by
  rintro L ⟨d, hd, hdec⟩
  have harg : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => false :: pairB [] x) :=
    cpt_cons1 false (cpt_pairB2 (cpt_const []) cpt_id)
  have hloop : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => (step d)^[x.length] (false :: pairB [] x)) :=
    cpt_iterGrow (cpt_step hd) 3 (step_len d) cpt_id harg
  have hlist : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => [dec d x]) :=
    cpt_comp hloop cpt_headOut
  obtain ⟨c⟩ := hlist
  refine ⟨dec d, ⟨⟨c.toTM2ComputableAux, c.time, c.outputsFun⟩⟩, ?_⟩
  intro x
  exact dec_iff hdec x

end PvsNP.Units.tc_closure_ins_one_p

theorem PvsNP.Units.tc_closure_ins_one_p :
    ∀ L : Language Bool, L ∈ PvsNP.P →
      ({x : List Bool | ∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ v ∈ L} :
        Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tc_closure_ins_one_p.closure_ins_one_p
