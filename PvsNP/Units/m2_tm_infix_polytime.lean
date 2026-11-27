import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime

/-
Built on the settled units PvsNP.Units.fr_ladner and PvsNP.Units.m2_eq_polytime of
github.com/makedotfun/pvsnp (Apache License 2.0), where fr_ladner's machine combinators come
from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_infix_polytime

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem encodePair_eq : encodePair = PvsNP.encodePair := by
  funext ⟨x, y⟩
  simp [encodePair, PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]

private theorem unOf_run (l : List Bool) :
    un l.length = fstRun (fun (_ : Unit) (_ : Bool) => ((), some true)) (fun _ => none) () l := by
  induction l with
  | nil => rfl
  | cons _ tl ih =>
    simp only [un, List.length_cons, List.replicate_succ, fstRun, Option.toList_some,
      List.cons_append, List.nil_append]
    exact congrArg (true :: ·) ih

private theorem cpt_unOf :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => un x.length) :=
  fst_polyTime _ _ _ (fun (_ : Unit) (_ : Bool) => ((), some true)) (fun _ => none) () unOf_run

private theorem takeWhile_un_false (n : ℕ) (y : List Bool) :
    (un n ++ false :: y).takeWhile id = un n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [un, List.replicate_succ, List.cons_append, List.takeWhile, id_eq] at ih ⊢
    exact congrArg (true :: ·) ih

private theorem dropWhile_un_false (n : ℕ) (y : List Bool) :
    (un n ++ false :: y).dropWhile id = false :: y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [un, List.replicate_succ, List.cons_append, List.dropWhile, id_eq] at ih ⊢
    exact ih

private theorem unpairB_un_false_fst (x y : List Bool) :
    (unpairB (un x.length ++ false :: y)).1 = y.take x.length := by
  rw [unpairB, takeWhile_un_false, dropWhile_un_false]
  simp [un]

private def isPref (x y : List Bool) : Bool :=
  decide ((unpairB (un x.length ++ false :: y)).1 = x)

private theorem isPref_iff (x y : List Bool) : isPref x y = true ↔ x <+: y := by
  simp only [isPref, unpairB_un_false_fst, decide_eq_true_eq]
  constructor
  · intro h
    refine ⟨y.drop x.length, ?_⟩
    have h2 := List.take_append_drop x.length y
    rw [h] at h2
    exact h2
  · rintro ⟨z, rfl⟩
    simp

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
  | cons b _ => cases b <;> simp [headBit, fstRun, headBitD, run_headBit_tail]

private theorem cpt_headBit :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) headBit :=
  fst_polyTime _ _ _ headBitD (fun _ => none) false run_headBit

private def firstD : Bool → Bool → Bool × Option Bool
  | false, b => (true, some b)
  | true, _ => (true, none)

private def headOutFin : Bool → Option Bool
  | false => some false
  | true => none

private theorem run_headOut_tail (l : List Bool) :
    fstRun firstD headOutFin true l = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simpa [fstRun, firstD] using ih

private theorem run_headOut (x : List Bool) :
    [x.headD false] = fstRun firstD headOutFin false x := by
  cases x with
  | nil => rfl
  | cons _ _ => simp [fstRun, firstD, run_headOut_tail]

private theorem cpt_headOut :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => [x.headD false]) :=
  fst_polyTime _ _ _ firstD headOutFin false run_headOut

private def step (s : List Bool) : List Bool :=
  let x := (unpairB s).1
  let ac := (unpairB s).2
  let cur := ac.tail
  let flag := headBit ac ++ (if isPref x cur then [true] else [])
  pairB x (sel flag (false :: cur.tail) (true :: cur.tail))

private theorem cpt_step :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) step := by
  have hx := cpt_unpairB1
  have hac := cpt_unpairB2
  have hcur := cpt_tail1 hac
  have htake := cpt_unpairB1_1 (cpt_app2 (cpt_comp hx cpt_unOf) (cpt_cons1 false hcur))
  have heq_p : ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.1 = p.2)) := by
    rw [encodePair_eq]
    exact PvsNP.Units.m2_eq_polytime
  have hprefFlag := cpt_bitFlag (cpt_comp (cpt_pair htake hx) heq_p)
  have hflag := cpt_app2 (cpt_comp hac cpt_headBit) hprefFlag
  have hcurTail := cpt_tail1 hcur
  exact cpt_pairB2 hx (cpt_sel hflag (cpt_cons1 false hcurTail) (cpt_cons1 true hcurTail))

private theorem step_len (s : List Bool) : (step s).length ≤ s.length + 2 := by
  have h1 := unpairB_length s
  have hsel : (sel (headBit (unpairB s).2 ++
      (if isPref (unpairB s).1 (unpairB s).2.tail then [true] else []))
      (false :: (unpairB s).2.tail.tail) (true :: (unpairB s).2.tail.tail)).length ≤
      (unpairB s).2.length + 1 := by
    by_cases h : headBit (unpairB s).2 ++
        (if isPref (unpairB s).1 (unpairB s).2.tail then [true] else []) = [] <;>
    · simp [sel, h]
      omega
  simp only [step, pairB_length]
  omega

private theorem step_pair (x cur : List Bool) (acc : Bool) :
    step (pairB x (acc :: cur)) = pairB x ((acc || isPref x cur) :: cur.tail) := by
  cases acc <;> cases hp : isPref x cur <;> simp [step, unpairB_pairB, sel, headBit, hp]

private def accOf (x y : List Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => accOf x y k || isPref x (y.drop k)

private theorem step_iter (x y : List Bool) : ∀ k : ℕ,
    step^[k] (pairB x (false :: y)) = pairB x (accOf x y k :: y.drop k)
  | 0 => by simp [accOf]
  | k + 1 => by
    rw [Function.iterate_succ_apply', step_iter x y k, step_pair]
    simp [accOf]

private theorem accOf_iff (x y : List Bool) : ∀ k : ℕ,
    accOf x y k = true ↔ ∃ j < k, x <+: y.drop j
  | 0 => by simp [accOf]
  | k + 1 => by
    show (accOf x y k || isPref x (y.drop k)) = true ↔ _
    rw [Bool.or_eq_true, accOf_iff x y k, isPref_iff]
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

private theorem factor_iff_drop (x y : List Bool) :
    x <:+: y ↔ ∃ j < y.length + 1, x <+: y.drop j := by
  constructor
  · rintro ⟨s, t, hst⟩
    refine ⟨s.length, ?_, ⟨t, ?_⟩⟩
    · have hlen := congrArg List.length hst
      simp only [List.length_append] at hlen
      omega
    · rw [← hst, List.append_assoc, List.drop_left]
  · rintro ⟨j, _, ⟨t, ht⟩⟩
    exact ⟨y.take j, t, by rw [List.append_assoc, ht, List.take_append_drop]⟩

private theorem factor_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.1 <:+: p.2)) := by
  have hloop := cpt_iterGrow cpt_step 2 step_len
    (cpt_cons1 true cpt_unpairB2)
    (cpt_pairB2 cpt_unpairB1 (cpt_cons1 false cpt_unpairB2))
  have hres := cpt_comp (cpt_unpairB2_1 hloop) cpt_headOut
  have h1 : ComputableInPolyTime encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => [decide (p.1 <:+: p.2)]) := by
    refine cpt_congr (cpt_comp cpt_pairB hres) ?_
    rintro ⟨x, y⟩
    show [((unpairB (step^[(true :: (unpairB (pairB x y)).2).length]
      (pairB (unpairB (pairB x y)).1 (false :: (unpairB (pairB x y)).2)))).2).headD false] =
      [decide (x <:+: y)]
    simp only [unpairB_pairB, List.length_cons, step_iter, List.headD_cons]
    congr 1
    rw [Bool.eq_iff_iff, accOf_iff, decide_eq_true_eq, factor_iff_drop]
  rw [encodePair_eq] at h1
  obtain ⟨c⟩ := h1
  exact ⟨⟨c.toTM2ComputableAux, c.time, c.outputsFun⟩⟩

end PvsNP.Units.m2_tm_infix_polytime

theorem PvsNP.Units.m2_tm_infix_polytime :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (p.1 <:+: p.2)) :=
  PvsNP.Units.m2_tm_infix_polytime.factor_polytime
