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

namespace PvsNP.Units.tc_closure_rotate_p

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

private theorem rotate_one (x : List Bool) : x.rotate 1 = x.tail ++ x.take 1 := by
  cases x with
  | nil => rfl
  | cons _ _ => simp

private theorem cpt_rot1 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x.rotate 1) := by
  have h : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x.tail ++ x.take 1) :=
    cpt_app2 (cpt_tail1 cpt_id) cpt_take1
  have e : (fun x : List Bool => x.rotate 1) = (fun x : List Bool => x.tail ++ x.take 1) :=
    funext rotate_one
  rw [e]
  exact h

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

private def orFlag (d : List Bool → Bool) (s : List Bool) : List Bool :=
  headBit s ++ (if d s.tail then [true] else [])

private def step (d : List Bool → Bool) (s : List Bool) : List Bool :=
  sel s [] (sel (orFlag d s) (false :: s.tail.rotate 1) (true :: s.tail.rotate 1))

private theorem step_cons (d : List Bool → Bool) (acc : Bool) (cur : List Bool) :
    step d (acc :: cur) = (acc || d cur) :: cur.rotate 1 := by
  cases acc <;> cases hd : d cur <;> simp [step, sel, orFlag, headBit, hd]

private theorem step_len (d : List Bool → Bool) (s : List Bool) :
    (step d s).length ≤ s.length := by
  cases s with
  | nil => simp [step, sel]
  | cons acc cur =>
    rw [step_cons]
    simp

private theorem cpt_step {d : List Bool → Bool}
    (hd : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool d) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (step d) := by
  have hrot : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => s.tail.rotate 1) :=
    cpt_comp (cpt_tail1 cpt_id) cpt_rot1
  have hdFlag : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => if d s.tail then [true] else []) :=
    cpt_bitFlag (cpt_comp (cpt_tail1 cpt_id) hd)
  have hor : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (orFlag d) :=
    cpt_app2 cpt_headBit hdFlag
  have hinner : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool =>
        sel (orFlag d s) (false :: s.tail.rotate 1) (true :: s.tail.rotate 1)) :=
    cpt_sel hor (cpt_cons1 false hrot) (cpt_cons1 true hrot)
  exact cpt_sel cpt_id (cpt_const []) hinner

private def accOf (d : List Bool → Bool) (x : List Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => accOf d x k || d (x.rotate k)

private theorem step_iter (d : List Bool → Bool) (x : List Bool) : ∀ k : ℕ,
    (step d)^[k] (false :: x) = accOf d x k :: x.rotate k
  | 0 => by simp [accOf]
  | k + 1 => by
    rw [Function.iterate_succ_apply', step_iter d x k, step_cons, List.rotate_rotate]
    rfl

private theorem accOf_iff (d : List Bool → Bool) (x : List Bool) : ∀ k : ℕ,
    accOf d x k = true ↔ ∃ j < k, d (x.rotate j) = true
  | 0 => by simp [accOf]
  | k + 1 => by
    show (accOf d x k || d (x.rotate k)) = true ↔ _
    rw [Bool.or_eq_true, accOf_iff d x k]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, by omega, h⟩
      · exact ⟨k, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      by_cases hjk : j < k
      · exact Or.inl ⟨j, hjk, h⟩
      · have hje : j = k := by omega
        subst hje
        exact Or.inr h

private def dec (d : List Bool → Bool) (x : List Bool) : Bool :=
  ((step d)^[(true :: x).length] (false :: x)).headD false

private theorem dec_iff {L : Language Bool} {d : List Bool → Bool}
    (hdec : ∀ x, x ∈ L ↔ d x = true) (x : List Bool) :
    (∃ k : ℕ, x.rotate k ∈ L) ↔ dec d x = true := by
  have heq : dec d x = accOf d x (x.length + 1) := by
    unfold dec
    rw [List.length_cons, step_iter]
    rfl
  rw [heq, accOf_iff]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hx : x = []
    · subst hx
      exact ⟨0, by omega, by simpa [hdec] using hk⟩
    · have hpos : 0 < x.length := List.length_pos_of_ne_nil hx
      refine ⟨k % x.length, by have := Nat.mod_lt k hpos; omega, ?_⟩
      rw [← hdec]
      simpa [List.rotate_mod] using hk
  · rintro ⟨j, _, hj⟩
    exact ⟨j, (hdec _).mpr hj⟩

private theorem closure_rotate_p :
    ∀ L : Language Bool, L ∈ PvsNP.P →
      ({x : List Bool | ∃ k : ℕ, x.rotate k ∈ L} : Language Bool) ∈ PvsNP.P := by
  rintro L ⟨d, hd, hdec⟩
  have hloop : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => (step d)^[(true :: x).length] (false :: x)) :=
    cpt_iterLen (cpt_step hd) (step_len d) (cpt_cons1 true cpt_id) (cpt_cons1 false cpt_id)
  have hlist : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => [dec d x]) :=
    cpt_comp hloop cpt_headOut
  obtain ⟨c⟩ := hlist
  refine ⟨dec d, ⟨⟨c.toTM2ComputableAux, c.time, c.outputsFun⟩⟩, ?_⟩
  intro x
  exact dec_iff hdec x

end PvsNP.Units.tc_closure_rotate_p

theorem PvsNP.Units.tc_closure_rotate_p :
    ∀ L : Language Bool, L ∈ PvsNP.P →
      ({x : List Bool | ∃ k : ℕ, x.rotate k ∈ L} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tc_closure_rotate_p.closure_rotate_p
