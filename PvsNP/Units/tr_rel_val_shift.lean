import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled campaign unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp
(Apache License 2.0), which carries the upstream PEqualNP library from
github.com/open-goat/pequalnp-proofs at commit 8df87a862bd9a618faecf10ba65bff72706442c9
(Apache License 2.0). Nothing from that unit is copied; it is imported directly.
The canonical bit-stripping, leading-zero split, equality flag, and power-of-two shift
decider below are original work for unit tr_rel_val_shift.
-/

set_option autoImplicit false

namespace PvsNP.Units.tr_rel_val_shift

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

private abbrev CPT (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f

private theorem cptU {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private theorem neU_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [fstRun, ih]

private theorem cpt_neU :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons b l => simp [fstRun, neU_true, Computability.encodeBool])

/-! ### Polynomial-time reversal, leading-false split, and equality flag -/

private def firstBit (rem : List Bool) : List Bool :=
  sel rem [] (sel (hd rem) [false] [true])

private theorem firstBit_len (rem : List Bool) : (firstBit rem).length ≤ 1 := by
  unfold firstBit sel
  split
  · simp
  · split <;> simp

private def revStep (st : List Bool) : List Bool :=
  let out := (unpairB st).1
  let rem := (unpairB st).2
  pairB (firstBit rem ++ out) rem.tail

private theorem revStep_len (st : List Bool) : (revStep st).length ≤ st.length + 3 := by
  unfold revStep
  dsimp only
  have h1 := unpairB_length st
  have h2 := firstBit_len (unpairB st).2
  have h3 : (unpairB st).2.tail.length ≤ (unpairB st).2.length := by
    cases (unpairB st).2 <;> simp
  simp only [pairB_length, List.length_append]
  omega

private theorem cpt_revStep : CPT revStep := by
  have hOut := cpt_unpairB1
  have hRem := cpt_unpairB2
  have hFb := cpt_sel hRem (cpt_const []) (cpt_sel (cpt_hd1 hRem) (cpt_const [false]) (cpt_const [true]))
  exact cptU (cpt_pairB2 (cpt_app2 hFb hOut) (cpt_comp hRem cpt_tail)) (fun _ => rfl)

private theorem revStep_iter : ∀ (rem out : List Bool),
    revStep^[rem.length] (pairB out rem) = pairB (rem.reverse ++ out) []
  | [], out => by simp
  | b :: rem, out => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : revStep (pairB out (b :: rem)) = pairB (b :: out) rem := by
      cases b <;> simp [revStep, firstBit, unpairB_pairB, hd, sel]
    rw [h1, revStep_iter rem (b :: out)]
    simp [List.reverse_cons, List.append_assoc]

private def revFn (l : List Bool) : List Bool :=
  (unpairB (revStep^[l.length] (pairB [] l))).1

private theorem revFn_eq (l : List Bool) : revFn l = l.reverse := by
  unfold revFn
  rw [revStep_iter, unpairB_pairB, List.append_nil]

private theorem cpt_revFn : CPT revFn :=
  cptU (cpt_unpairB1_1 (cpt_iterGrow cpt_revStep 3 revStep_len cpt_id (cpt_pairB2 (cpt_const []) cpt_id)))
    (fun _ => rfl)

private def dropFalseD : Bool → Bool → Bool × Option Bool
  | false, false => (false, none)
  | false, true => (true, some true)
  | true, b => (true, some b)

private theorem dropFalseD_true (l : List Bool) :
    fstRun dropFalseD (fun _ => none) true l = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [fstRun, dropFalseD] using ih

private def dropFalse (l : List Bool) : List Bool :=
  fstRun dropFalseD (fun _ => none) false l

private theorem dropFalse_eq (l : List Bool) :
    dropFalse l = l.dropWhile (fun b => !b) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b with
    | false =>
      simp only [dropFalse, fstRun, dropFalseD, Option.toList_none, List.nil_append,
        List.dropWhile_cons, Bool.not_false, ↓reduceIte]
      exact ih
    | true =>
      simp [dropFalse, fstRun, dropFalseD, dropFalseD_true]

private theorem cpt_dropFalse : CPT dropFalse :=
  fst_polyTime _ _ _ dropFalseD (fun _ => none) false (fun _ => rfl)

private def takeFalseD : Bool → Bool → Bool × Option Bool
  | false, false => (false, some false)
  | false, true => (true, none)
  | true, _ => (true, none)

private theorem takeFalseD_true (l : List Bool) :
    fstRun takeFalseD (fun _ => none) true l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [fstRun, takeFalseD] using ih

private def takeFalse (l : List Bool) : List Bool :=
  fstRun takeFalseD (fun _ => none) false l

private theorem takeFalse_eq (l : List Bool) :
    takeFalse l = l.takeWhile (fun b => !b) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b with
    | false =>
      simp only [takeFalse, fstRun, takeFalseD, Option.toList_some, List.singleton_append,
        List.takeWhile_cons, Bool.not_false, ↓reduceIte]
      exact congrArg (false :: ·) ih
    | true =>
      simp [takeFalse, fstRun, takeFalseD, takeFalseD_true]

private theorem cpt_takeFalse : CPT takeFalse :=
  fst_polyTime _ _ _ takeFalseD (fun _ => none) false (fun _ => rfl)

private def stripFn (l : List Bool) : List Bool :=
  revFn (dropFalse (revFn l))

private theorem stripFn_eq (l : List Bool) :
    stripFn l = (l.reverse.dropWhile (fun b => !b)).reverse := by
  simp [stripFn, revFn_eq, dropFalse_eq]

private theorem cpt_stripFn : CPT stripFn :=
  cptU (cpt_comp (cpt_comp cpt_revFn cpt_dropFalse) cpt_revFn) (fun _ => rfl)

private def headBitEq (a b : List Bool) : List Bool :=
  sel (hd a) (sel (hd b) [true] []) (sel (hd b) [] [true])

private theorem headBitEq_len (a b : List Bool) : (headBitEq a b).length ≤ 1 := by
  unfold headBitEq sel
  split <;> split <;> simp

private def eqStep (st : List Bool) : List Bool :=
  let ok := (unpairB st).1
  let a := (unpairB (unpairB st).2).1
  let b := (unpairB (unpairB st).2).2
  let bothNil := pairB (sel ok [] [true]) (pairB [] [])
  let bothCons := pairB (sel ok [] (headBitEq a b)) (pairB a.tail b.tail)
  let mismatch := pairB [] (pairB [] [])
  sel a (sel b bothNil mismatch) (sel b mismatch bothCons)

private theorem eqStep_len (st : List Bool) : (eqStep st).length ≤ st.length + 4 := by
  unfold eqStep
  dsimp only
  set ok := (unpairB st).1
  set r := (unpairB st).2
  set a := (unpairB r).1
  set b := (unpairB r).2
  have h1 : 2 * ok.length + r.length ≤ st.length := unpairB_length st
  have h2 : 2 * a.length + b.length ≤ r.length := unpairB_length r
  have ha : a.tail.length ≤ a.length := by cases a <;> simp
  have hb : b.tail.length ≤ b.length := by cases b <;> simp
  have hok1 : (sel ok [] [true]).length ≤ 1 := by unfold sel; split <;> simp
  have hok2 : (sel ok [] (headBitEq a b)).length ≤ 1 := by
    have := headBitEq_len a b
    unfold sel; split <;> simp [this]
  simp only [sel] at hok1 hok2 ⊢
  split
  · split <;> simp only [pairB_length, List.length_nil] <;> omega
  · split <;> simp only [pairB_length, List.length_nil] <;> omega

private theorem cpt_eqStep : CPT eqStep := by
  have hOk := cpt_unpairB1
  have hR := cpt_unpairB2
  have hA := cpt_unpairB1_1 hR
  have hB := cpt_unpairB2_1 hR
  have hHbe : CPT (fun s => headBitEq (unpairB (unpairB s).2).1 (unpairB (unpairB s).2).2) :=
    cpt_sel (cpt_hd1 hA) (cpt_sel (cpt_hd1 hB) (cpt_const [true]) (cpt_const []))
      (cpt_sel (cpt_hd1 hB) (cpt_const []) (cpt_const [true]))
  have hNil := cpt_pairB2 (cpt_sel hOk (cpt_const []) (cpt_const [true]))
    (cpt_pairB2 (cpt_const []) (cpt_const []))
  have hCons := cpt_pairB2 (cpt_sel hOk (cpt_const []) hHbe)
    (cpt_pairB2 (cpt_comp hA cpt_tail) (cpt_comp hB cpt_tail))
  have hMis := cpt_pairB2 (cpt_const []) (cpt_pairB2 (cpt_const []) (cpt_const []))
  exact cptU (cpt_sel hA (cpt_sel hB hNil hMis) (cpt_sel hB hMis hCons)) (fun _ => rfl)

private def eqFlag (a b : List Bool) : List Bool :=
  (unpairB (eqStep^[a.length + 1] (pairB [true] (pairB a b)))).1

private theorem cpt_eqFlag {u v : List Bool → List Bool} (hu : CPT u) (hv : CPT v) :
    CPT (fun s => eqFlag (u s) (v s)) := by
  have hCnt : CPT (fun s => true :: u s) := cpt_cons1 true hu
  have hInit := cpt_pairB2 (cpt_const [true]) (cpt_pairB2 hu hv)
  have hIt := cpt_iterGrow cpt_eqStep 4 eqStep_len hCnt hInit
  exact cptU (cpt_unpairB1_1 hIt) (fun s => by simp [eqFlag])

private theorem eqStep_ok_nil (st : List Bool) (h : (unpairB st).1 = []) :
    (unpairB (eqStep st)).1 = [] := by
  unfold eqStep
  dsimp only
  rw [h]
  unfold sel
  split
  · split <;> simp [unpairB_pairB]
  · split <;> simp [unpairB_pairB]

private theorem eqStep_iter_ok_nil (m : ℕ) (st : List Bool) (h : (unpairB st).1 = []) :
    (unpairB (eqStep^[m] st)).1 = [] := by
  induction m generalizing st with
  | zero => exact h
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (eqStep_ok_nil st h)

private theorem eqFlag_ne_nil_iff : ∀ a b : List Bool, eqFlag a b ≠ [] ↔ a = b
  | [], [] => by simp [eqFlag, eqStep, unpairB_pairB, sel]
  | [], _ :: _ => by simp [eqFlag, eqStep, unpairB_pairB, sel]
  | x :: a, [] => by
    unfold eqFlag
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : eqStep (pairB [true] (pairB (x :: a) [])) = pairB [] (pairB [] []) := by
      simp [eqStep, unpairB_pairB, sel]
    rw [h1, eqStep_iter_ok_nil _ _ (by simp [unpairB_pairB])]
    simp
  | x :: a, y :: b => by
    unfold eqFlag
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : eqStep (pairB [true] (pairB (x :: a) (y :: b))) =
        pairB (headBitEq (x :: a) (y :: b)) (pairB a b) := by
      simp [eqStep, unpairB_pairB, sel]
    rw [h1]
    cases x <;> cases y
    · have hh : headBitEq (false :: a) (false :: b) = [true] := by simp [headBitEq, hd, sel]
      rw [hh]
      have ih := eqFlag_ne_nil_iff a b
      simpa [eqFlag] using ih
    · have hh : headBitEq (false :: a) (true :: b) = [] := by simp [headBitEq, hd, sel]
      rw [hh, eqStep_iter_ok_nil _ _ (by simp [unpairB_pairB])]
      simp
    · have hh : headBitEq (true :: a) (false :: b) = [] := by simp [headBitEq, hd, sel]
      rw [hh, eqStep_iter_ok_nil _ _ (by simp [unpairB_pairB])]
      simp
    · have hh : headBitEq (true :: a) (true :: b) = [true] := by simp [headBitEq, hd, sel]
      rw [hh]
      have ih := eqFlag_ne_nil_iff a b
      simpa [eqFlag] using ih

/-! ### Binary arithmetic lemmas -/

private theorem all_false_of_dropWhile_nil : ∀ r : List Bool,
    r.dropWhile (fun c => !c) = [] → ∀ c ∈ r, c = false
  | [], _, _, h => by simp at h
  | true :: _, h, _, _ => by simp at h
  | false :: r, h, c, hc => by
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc'
    · rfl
    · exact all_false_of_dropWhile_nil r (by simpa using h) c hc'

private theorem ofDigits_eq_zero_of_all_false : ∀ u : List Bool,
    (∀ c ∈ u, c = false) → Nat.ofDigits 2 (u.map Bool.toNat) = 0
  | [], _ => rfl
  | c :: u, h => by
    have hc : c = false := h c (by simp)
    have hu : ∀ x ∈ u, x = false := fun x hx => h x (by simp [hx])
    simp [hc, Nat.ofDigits_cons, ofDigits_eq_zero_of_all_false u hu]

private theorem dropWhile_append_of_nil : ∀ (r t : List Bool),
    r.dropWhile (fun c => !c) = [] →
      (r ++ t).dropWhile (fun c => !c) = t.dropWhile (fun c => !c)
  | [], _, _ => rfl
  | true :: _, _, h => by simp at h
  | false :: r, t, h => by
    simpa using dropWhile_append_of_nil r t (by simpa using h)

private theorem dropWhile_append_of_ne_nil : ∀ (r t : List Bool),
    r.dropWhile (fun c => !c) ≠ [] →
      (r ++ t).dropWhile (fun c => !c) = r.dropWhile (fun c => !c) ++ t
  | [], _, h => absurd rfl h
  | true :: _, _, _ => by simp
  | false :: r, t, h => by
    simpa using dropWhile_append_of_ne_nil r t (by simpa using h)

private theorem strip_eq_bits : ∀ u : List Bool,
    (u.reverse.dropWhile (fun b => !b)).reverse = Nat.bits (Nat.ofDigits 2 (u.map Bool.toNat))
  | [] => by simp
  | b :: u => by
    simp only [List.reverse_cons, List.map_cons, Nat.ofDigits_cons]
    have ih := strip_eq_bits u
    by_cases hdw : u.reverse.dropWhile (fun c => !c) = []
    · have hall : ∀ c ∈ u, c = false := fun c hc =>
        all_false_of_dropWhile_nil u.reverse hdw c (List.mem_reverse.mpr hc)
      have h0 : Nat.ofDigits 2 (u.map Bool.toNat) = 0 := ofDigits_eq_zero_of_all_false u hall
      rw [dropWhile_append_of_nil u.reverse [b] hdw, h0]
      cases b <;> simp
    · rw [dropWhile_append_of_ne_nil u.reverse [b] hdw, List.reverse_append]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      have hne0 : Nat.ofDigits 2 (u.map Bool.toNat) ≠ 0 := by
        intro h0
        rw [h0, Nat.zero_bits] at ih
        exact hdw (List.reverse_eq_nil_iff.mp ih)
      rw [ih]
      cases b with
      | false =>
        simp only [Bool.toNat_false, zero_add]
        rw [Nat.bit0_bits _ hne0]
      | true =>
        simp only [Bool.toNat_true]
        rw [Nat.add_comm, Nat.bit1_bits]

private theorem ofDigits_bits (n : ℕ) :
    Nat.ofDigits 2 ((Nat.bits n).map Bool.toNat) = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn : n = 0
    · subst hn; simp
    · have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num)
      have ih' := ih (n / 2) hlt
      rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
      · have hm : m ≠ 0 := fun h => hn (by simp [h])
        have hdiv : (2 * m) / 2 = m := by omega
        rw [hdiv] at ih'
        rw [Nat.bit0_bits m hm, List.map_cons, Nat.ofDigits_cons, Bool.toNat_false, zero_add, ih']
      · have hdiv : (2 * m + 1) / 2 = m := by omega
        rw [hdiv] at ih'
        rw [Nat.bit1_bits m, List.map_cons, Nat.ofDigits_cons, Bool.toNat_true, ih']
        omega

private theorem bits_inj {m n : ℕ} (h : Nat.bits m = Nat.bits n) : m = n := by
  rw [← ofDigits_bits m, ← ofDigits_bits n, h]

private theorem bits_mul_two_pow (n : ℕ) (hn : n ≠ 0) :
    ∀ k : ℕ, Nat.bits (n * 2 ^ k) = List.replicate k false ++ Nat.bits n
  | 0 => by simp
  | k + 1 => by
    have hne : n * 2 ^ k ≠ 0 := Nat.mul_ne_zero hn (pow_ne_zero k (by norm_num))
    have heq : n * 2 ^ (k + 1) = 2 * (n * 2 ^ k) := by rw [Nat.pow_succ]; ring
    rw [heq, Nat.bit0_bits _ hne, bits_mul_two_pow n hn k, List.replicate_succ, List.cons_append]

private theorem takeWhile_not_eq_rep : ∀ l : List Bool,
    l.takeWhile (fun b => !b) = List.replicate (l.takeWhile (fun b => !b)).length false
  | [] => rfl
  | true :: _ => rfl
  | false :: l => by
    simp only [List.takeWhile_cons, Bool.not_false, ↓reduceIte, List.length_cons, List.replicate_succ]
    exact congrArg (false :: ·) (takeWhile_not_eq_rep l)

private theorem takeWhile_rep_false (k : ℕ) (a : List Bool) :
    (List.replicate k false ++ a).takeWhile (fun b => !b) =
      List.replicate k false ++ a.takeWhile (fun b => !b) := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

private theorem dropWhile_rep_false (k : ℕ) (a : List Bool) :
    (List.replicate k false ++ a).dropWhile (fun b => !b) = a.dropWhile (fun b => !b) := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

private theorem strip_eq_nil_of_dropWhile_nil (l : List Bool)
    (h : (l.reverse.dropWhile (fun c => !c)).reverse.dropWhile (fun c => !c) = []) :
    (l.reverse.dropWhile (fun c => !c)).reverse = [] := by
  have hall := all_false_of_dropWhile_nil _ h
  cases hr : l.reverse.dropWhile (fun c => !c) with
  | nil => simp
  | cons c rs =>
    have hc : c = true := by
      have hhead : ∀ t : List Bool, t.dropWhile (fun b => !b) = c :: rs → c = true := by
        intro t
        induction t with
        | nil => intro h0; simp at h0
        | cons b ts ih =>
          intro h0
          cases b with
          | false => exact ih (by simpa using h0)
          | true => simp at h0; exact h0.1
      exact hhead l.reverse hr
    have hmem : c ∈ (c :: rs).reverse := List.mem_reverse.mpr (by simp)
    rw [hr] at hall
    have hcf := hall c hmem
    rw [hc] at hcf
    exact absurd hcf (by decide)

/-! ### Decider and correctness -/

private def shiftFlag (s : List Bool) : List Bool :=
  let a := stripFn (unpairB s).1
  let b := stripFn (unpairB s).2
  let eqD := eqFlag (dropFalse a) (dropFalse b)
  let leT := if decide ((takeFalse a).length ≤ (takeFalse b).length) then [true] else []
  sel eqD [] leT

private theorem cpt_shiftFlag : CPT shiftFlag := by
  have hA := cpt_comp cpt_unpairB1 cpt_stripFn
  have hB := cpt_comp cpt_unpairB2 cpt_stripFn
  have hEqD := cpt_eqFlag (cpt_comp hA cpt_dropFalse) (cpt_comp hB cpt_dropFalse)
  have hLeT := cpt_le (cpt_comp hA cpt_takeFalse) (cpt_comp hB cpt_takeFalse)
  exact cptU (cpt_sel hEqD (cpt_const []) hLeT) (fun _ => rfl)

private def shiftDec (p : List Bool × List Bool) : Bool :=
  !(shiftFlag (pairB p.1 p.2)).isEmpty

private theorem cpt_shiftDec :
    ComputableInPolyTime encodePair Computability.encodeBool shiftDec :=
  cptU (cpt_comp cpt_pairB (cpt_comp cpt_shiftFlag cpt_neU)) (fun _ => rfl)

theorem val_shift_main :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
        ∀ p : List Bool × List Bool,
          (∃ k : ℕ, Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) =
              Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * 2 ^ k) ↔ f p = true := by
  refine ⟨shiftDec, cpt_shiftDec, fun p => ?_⟩
  obtain ⟨x, y⟩ := p
  set vx := Nat.ofDigits 2 (x.map Bool.toNat)
  set vy := Nat.ofDigits 2 (y.map Bool.toNat)
  set a := (x.reverse.dropWhile (fun b => !b)).reverse
  set b := (y.reverse.dropWhile (fun b => !b)).reverse
  have ha_bits : a = Nat.bits vx := strip_eq_bits x
  have hb_bits : b = Nat.bits vy := strip_eq_bits y
  have hdec : shiftDec (x, y) = true ↔
      a.dropWhile (fun c => !c) = b.dropWhile (fun c => !c) ∧
        (a.takeWhile (fun c => !c)).length ≤ (b.takeWhile (fun c => !c)).length := by
    simp only [shiftDec, shiftFlag, unpairB_pairB, stripFn_eq, dropFalse_eq, takeFalse_eq,
      Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq]
    change sel (eqFlag (a.dropWhile (fun c => !c)) (b.dropWhile (fun c => !c))) []
      (if decide ((a.takeWhile (fun c => !c)).length ≤ (b.takeWhile (fun c => !c)).length)
        then [true] else []) ≠ [] ↔ _
    by_cases hd : a.dropWhile (fun c => !c) = b.dropWhile (fun c => !c)
    · have hne : eqFlag (a.dropWhile (fun c => !c)) (b.dropWhile (fun c => !c)) ≠ [] :=
        (eqFlag_ne_nil_iff _ _).mpr hd
      simp only [sel, hne, ↓reduceIte]
      simp only [hd, true_and]
      by_cases hl : (a.takeWhile (fun c => !c)).length ≤ (b.takeWhile (fun c => !c)).length
      · simp [hl]
      · simp [hl]
    · have heq : eqFlag (a.dropWhile (fun c => !c)) (b.dropWhile (fun c => !c)) = [] := by
        by_contra hne
        exact hd ((eqFlag_ne_nil_iff _ _).mp hne)
      simp [sel, heq, hd]
  rw [hdec]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hx0 : vx = 0
    · have hy0 : vy = 0 := by rw [hk, hx0, zero_mul]
      have ha0 : a = [] := by rw [ha_bits, hx0, Nat.zero_bits]
      have hb0 : b = [] := by rw [hb_bits, hy0, Nat.zero_bits]
      simp [ha0, hb0]
    · have hb_eq : b = List.replicate k false ++ a := by
        rw [hb_bits, hk, bits_mul_two_pow vx hx0 k, ha_bits]
      rw [hb_eq, dropWhile_rep_false, takeWhile_rep_false, List.length_append, List.length_replicate]
      exact ⟨rfl, by omega⟩
  · rintro ⟨hdrop, hle⟩
    by_cases hx0 : vx = 0
    · have ha0 : a = [] := by rw [ha_bits, hx0, Nat.zero_bits]
      have hbdw : b.dropWhile (fun c => !c) = [] := by rw [← hdrop, ha0]; rfl
      have hb0 : b = [] := strip_eq_nil_of_dropWhile_nil y hbdw
      have hy0 : vy = 0 := bits_inj (by rw [← hb_bits, hb0, Nat.zero_bits])
      exact ⟨0, by simp [hx0, hy0]⟩
    · set k := (b.takeWhile (fun c => !c)).length - (a.takeWhile (fun c => !c)).length
      have hb_eq : b = List.replicate k false ++ a := by
        calc b = b.takeWhile (fun c => !c) ++ b.dropWhile (fun c => !c) :=
            (List.takeWhile_append_dropWhile (p := fun c => !c) (l := b)).symm
          _ = List.replicate (b.takeWhile (fun c => !c)).length false ++ a.dropWhile (fun c => !c) := by
            rw [← hdrop]
            conv_lhs => rw [takeWhile_not_eq_rep b]
          _ = List.replicate (k + (a.takeWhile (fun c => !c)).length) false ++ a.dropWhile (fun c => !c) := by
            rw [show k + (a.takeWhile (fun c => !c)).length = (b.takeWhile (fun c => !c)).length by omega]
          _ = List.replicate k false ++
              (List.replicate (a.takeWhile (fun c => !c)).length false ++ a.dropWhile (fun c => !c)) := by
            rw [List.replicate_add, List.append_assoc]
          _ = List.replicate k false ++ (a.takeWhile (fun c => !c) ++ a.dropWhile (fun c => !c)) := by
            rw [← takeWhile_not_eq_rep a]
          _ = List.replicate k false ++ a := by
            rw [List.takeWhile_append_dropWhile (p := fun c => !c) (l := a)]
      refine ⟨k, bits_inj ?_⟩
      rw [← hb_bits, hb_eq, ha_bits, bits_mul_two_pow vx hx0 k]

end PvsNP.Units.tr_rel_val_shift

theorem PvsNP.Units.tr_rel_val_shift :
    ∃ f : List Bool × List Bool → Bool,
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
        ∀ p : List Bool × List Bool,
          (∃ k : ℕ, Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) =
              Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * 2 ^ k) ↔ f p = true :=
  PvsNP.Units.tr_rel_val_shift.val_shift_main
