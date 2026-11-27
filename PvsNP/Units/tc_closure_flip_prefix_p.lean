import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp (Apache License
2.0), whose machine combinators come from github.com/open-goat/pequalnp-proofs (formerly
brilliant-hq/pequalnp-proofs) at commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License
2.0). The rotation step of the settled unit PvsNP.Units.tc_closure_rotate_p (same family
`tc_closure`, class `p`) is replaced by a prefix-flip step: the machine walks the split
point `i` from `0` to `n`, keeping the reversed prefix and the remaining suffix, and tests
the decider of `L` on `revPre ++ suf` at each split. The `head1` machine and the `headD`
extraction are copied from the settled `tc_closure_rotate_p` unit and the
`tc_closure_del_one_conp` draft (same upstream origin).
-/

set_option autoImplicit false

namespace PvsNP.Units.tc_closure_flip_prefix_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private def head1 : List Bool → List Bool
  | [] => []
  | b :: _ => [b]

private def head1δ : Bool → Bool → Bool × Option Bool
  | false, b => (true, some b)
  | true, _ => (true, none)

private def head1Fin : Bool → Option Bool := fun _ => none

private theorem head1_run_true (x : List Bool) : fstRun head1δ head1Fin true x = [] := by
  induction x with
  | nil => rfl
  | cons _ t ih => simp [fstRun, head1δ, ih]

private theorem head1_run_false (x : List Bool) : fstRun head1δ head1Fin false x = head1 x := by
  cases x with
  | nil => rfl
  | cons b t => simp [fstRun, head1δ, head1_run_true, head1]

private theorem cpt_head1 :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) head1 :=
  fst_polyTime (fun x : List Bool => x) (fun x : List Bool => x) head1 head1δ head1Fin false
    (fun x => (head1_run_false x).symm)

private theorem head1_length (s : List Bool) : (head1 s).length ≤ 1 := by
  cases s <;> simp [head1]

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

/-- One flip-prefix step: test `d (pre ++ suf)` and OR the result into the flag,
then move the head of `suf` onto the front of the reversed prefix `pre`.
State is `pairB flag (pairB pre suf)`. -/
private def fstep (d : List Bool → Bool) (s : List Bool) : List Bool :=
  let flag := (unpairB s).1
  let rest := (unpairB s).2
  let pre := (unpairB rest).1
  let suf := (unpairB rest).2
  pairB (sel flag (if d (pre ++ suf) then [true] else []) [true])
    (pairB (head1 suf ++ pre) suf.tail)

private theorem fstep_pairB (d : List Bool → Bool) (flag pre suf : List Bool) :
    fstep d (pairB flag (pairB pre suf)) =
      pairB (sel flag (if d (pre ++ suf) then [true] else []) [true])
        (pairB (head1 suf ++ pre) suf.tail) := by
  simp [fstep, unpairB_pairB]

private theorem flag_length (flag : List Bool) (b : Bool) :
    (sel flag (if b then [true] else []) [true]).length ≤ 1 :=
  sel_length flag _ _ 1 (by cases b <;> simp) (by simp)

private theorem fstep_length (d : List Bool → Bool) (s : List Bool) :
    (fstep d s).length ≤ s.length + 6 := by
  dsimp only [fstep]
  simp only [pairB_length, List.length_append, List.length_tail]
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).2
  have hhead := head1_length (unpairB (unpairB s).2).2
  have hflag := flag_length (unpairB s).1
    (d ((unpairB (unpairB s).2).1 ++ (unpairB (unpairB s).2).2))
  omega

private theorem cpt_fstep {d : List Bool → Bool}
    (hd : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool d) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (fstep d) := by
  have hflag := cpt_unpairB1
  have hrest := cpt_unpairB2
  have hpre := cpt_unpairB1_1 hrest
  have hsuf := cpt_unpairB2_1 hrest
  have htest : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).1 ++ (unpairB (unpairB s).2).2) :=
    cpt_app2 hpre hsuf
  have hdtest : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s => d ((unpairB (unpairB s).2).1 ++ (unpairB (unpairB s).2).2)) :=
    cpt_comp htest hd
  have hbit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => if d ((unpairB (unpairB s).2).1 ++ (unpairB (unpairB s).2).2)
        then [true] else []) :=
    cpt_bitFlag hdtest
  have hflag' : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => sel (unpairB s).1
        (if d ((unpairB (unpairB s).2).1 ++ (unpairB (unpairB s).2).2)
          then [true] else [])
        [true]) :=
    cpt_sel hflag hbit (cpt_const [true])
  have hpre' : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => head1 (unpairB (unpairB s).2).2 ++ (unpairB (unpairB s).2).1) :=
    cpt_app2 (cpt_comp hsuf cpt_head1) hpre
  have hsuf' : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s => (unpairB (unpairB s).2).2.tail) :=
    cpt_tail1 hsuf
  exact cpt_pairB2 hflag' (cpt_pairB2 hpre' hsuf')

private def accOf (d : List Bool → Bool) (x : List Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => accOf d x k || d ((x.take k).reverse ++ x.drop k)

private theorem take_succ_reverse (x : List Bool) (k : ℕ) :
    (x.take (k + 1)).reverse = head1 (x.drop k) ++ (x.take k).reverse := by
  induction x generalizing k with
  | nil =>
    cases k with
    | zero => rfl
    | succ j => rfl
  | cons b t ih =>
    cases k with
    | zero => rfl
    | succ j =>
      simp only [List.take_succ_cons, List.drop_succ_cons, List.reverse_cons]
      rw [ih j, List.append_assoc]

private theorem drop_succ_tail (s : List Bool) (j : ℕ) :
    s.drop (j + 1) = (s.drop j).tail := by
  induction s generalizing j with
  | nil => cases j <;> rfl
  | cons b t ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

private theorem sel_flag_or (a b : Bool) :
    sel (if a then [true] else []) (if b then [true] else []) [true] =
      if a || b then [true] else [] := by
  cases a <;> cases b <;> rfl

private theorem fstep_iter (d : List Bool → Bool) (x : List Bool) : ∀ k : ℕ,
    (fstep d)^[k] (pairB [] (pairB [] x)) =
      pairB (if accOf d x k then [true] else [])
        (pairB ((x.take k).reverse) (x.drop k))
  | 0 => by simp [accOf]
  | k + 1 => by
    rw [Function.iterate_succ_apply', fstep_iter d x k, fstep_pairB, take_succ_reverse,
      drop_succ_tail, sel_flag_or]
    rfl

private theorem accOf_iff (d : List Bool → Bool) (x : List Bool) : ∀ k : ℕ,
    accOf d x k = true ↔ ∃ j < k, d ((x.take j).reverse ++ x.drop j) = true
  | 0 => by simp [accOf]
  | k + 1 => by
    show (accOf d x k || d ((x.take k).reverse ++ x.drop k)) = true ↔ _
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

private def run (d : List Bool → Bool) (x : List Bool) : List Bool :=
  (fstep d)^[x.length + 1] (pairB [] (pairB [] x))

private def dec (d : List Bool → Bool) (x : List Bool) : Bool :=
  ((unpairB (run d x)).1).headD false

private theorem dec_eq_accOf (d : List Bool → Bool) (x : List Bool) :
    dec d x = accOf d x (x.length + 1) := by
  unfold dec run
  rw [fstep_iter, unpairB_pairB]
  cases hacc : accOf d x (x.length + 1) <;> simp

private theorem dec_iff {L : Language Bool} {d : List Bool → Bool}
    (hdec : ∀ x, x ∈ L ↔ d x = true) (x : List Bool) :
    (∃ i : ℕ, (x.take i).reverse ++ x.drop i ∈ L) ↔ dec d x = true := by
  rw [dec_eq_accOf, accOf_iff]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hle : i ≤ x.length
    · exact ⟨i, by omega, (hdec _).mp hi⟩
    · have htake : x.take i = x := List.take_of_length_le (by omega)
      have hdrop : x.drop i = [] := List.drop_of_length_le (by omega)
      refine ⟨x.length, by omega, ?_⟩
      have heq : (x.take x.length).reverse ++ x.drop x.length =
          (x.take i).reverse ++ x.drop i := by
        rw [List.take_length, List.drop_length, htake, hdrop]
      rw [heq]
      exact (hdec _).mp hi
  · rintro ⟨j, _, hj⟩
    exact ⟨j, (hdec _).mpr hj⟩

private theorem closure_flip_prefix_p :
    ∀ L : Language Bool, L ∈ PvsNP.P →
      ({x : List Bool | ∃ i : ℕ, (x.take i).reverse ++ x.drop i ∈ L} : Language Bool) ∈ PvsNP.P := by
  rintro L ⟨d, hd, hdec⟩
  have hcnt : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => true :: x) :=
    cpt_cons1 true cpt_id
  have hinit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => pairB [] (pairB [] x)) :=
    cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) cpt_id)
  have hloop : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => (fstep d)^[x.length + 1] (pairB [] (pairB [] x))) :=
    cpt_iterGrow (g := fstep d) (cnt := fun x : List Bool => true :: x)
      (arg := fun x : List Bool => pairB [] (pairB [] x))
      (cpt_fstep hd) 6 (fstep_length d) hcnt hinit
  have hflag : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => (unpairB ((fstep d)^[x.length + 1] (pairB [] (pairB [] x)))).1) :=
    cpt_unpairB1_1 hloop
  have hlist : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => [dec d x]) :=
    cpt_comp hflag cpt_headOut
  obtain ⟨c⟩ := hlist
  refine ⟨dec d, ⟨⟨c.toTM2ComputableAux, c.time, c.outputsFun⟩⟩, ?_⟩
  intro x
  exact dec_iff hdec x

end PvsNP.Units.tc_closure_flip_prefix_p

theorem PvsNP.Units.tc_closure_flip_prefix_p :
    ∀ L : Language Bool, L ∈ PvsNP.P →
      ({x : List Bool | ∃ i : ℕ, (x.take i).reverse ++ x.drop i ∈ L} : Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tc_closure_flip_prefix_p.closure_flip_prefix_p
