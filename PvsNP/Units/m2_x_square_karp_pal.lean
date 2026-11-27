import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled campaign unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp
(Apache License 2.0), which carries the upstream PEqualNP library from
github.com/open-goat/pequalnp-proofs at commit 8df87a862bd9a618faecf10ba65bff72706442c9
(Apache License 2.0). Nothing from that unit is copied; it is imported directly.
The half-split transducer, string-equality flag, and Karp reduction from squares to
palindromes below are original work for unit m2_x_square_karp_pal.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_x_square_karp_pal

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private abbrev CPT (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f

private theorem cptU {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

private def halfD : Bool → Bool → Bool × Option Bool
  | false, _ => (true, none)
  | true, _ => (false, some true)

private def halfLen (l : List Bool) : List Bool :=
  fstRun halfD (fun _ => none) false l

private theorem halfLen_length : ∀ l : List Bool, (halfLen l).length = l.length / 2
  | [] => rfl
  | [_] => by simp [halfLen, fstRun, halfD]
  | _ :: _ :: l => by
    have ih := halfLen_length l
    simp only [halfLen, fstRun, halfD, Option.toList_none, Option.toList_some,
      List.nil_append, List.cons_append, List.length_cons] at ih ⊢
    omega

private theorem cpt_halfLen : CPT halfLen :=
  fst_polyTime _ _ _ halfD (fun _ => none) false (fun _ => rfl)

private def firstBit (rem : List Bool) : List Bool :=
  sel rem [] (sel (hd rem) [false] [true])

private theorem firstBit_len (rem : List Bool) : (firstBit rem).length ≤ 1 := by
  unfold firstBit sel
  split
  · simp
  · split <;> simp

private def takeStep (st : List Bool) : List Bool :=
  let out := (unpairB st).1
  let rem := (unpairB st).2
  pairB (out ++ firstBit rem) rem.tail

private theorem takeStep_len (st : List Bool) : (takeStep st).length ≤ st.length + 3 := by
  unfold takeStep
  dsimp only
  have h1 := unpairB_length st
  have h2 := firstBit_len (unpairB st).2
  have h3 : (unpairB st).2.tail.length ≤ (unpairB st).2.length := by
    cases (unpairB st).2 <;> simp
  simp only [pairB_length, List.length_append]
  omega

private theorem cpt_takeStep : CPT takeStep := by
  have hOut := cpt_unpairB1
  have hRem := cpt_unpairB2
  have hFb := cpt_sel hRem (cpt_const []) (cpt_sel (cpt_hd1 hRem) (cpt_const [false]) (cpt_const [true]))
  exact cptU (cpt_pairB2 (cpt_app2 hOut hFb) (cpt_comp hRem cpt_tail)) (fun _ => rfl)

private theorem takeStep_iter : ∀ (k : ℕ) (out rem : List Bool),
    takeStep^[k] (pairB out rem) = pairB (out ++ rem.take k) (rem.drop k)
  | 0, out, rem => by simp
  | k + 1, out, [] => by
    rw [Function.iterate_succ_apply]
    have h1 : takeStep (pairB out []) = pairB out [] := by
      simp [takeStep, firstBit, unpairB_pairB, sel]
    rw [h1, takeStep_iter k out []]
    simp
  | k + 1, out, b :: rem => by
    rw [Function.iterate_succ_apply]
    have h1 : takeStep (pairB out (b :: rem)) = pairB (out ++ [b]) rem := by
      cases b <;> simp [takeStep, firstBit, unpairB_pairB, hd, sel]
    rw [h1, takeStep_iter k (out ++ [b]) rem]
    simp [List.append_assoc]

private def splitHalf (x : List Bool) : List Bool :=
  takeStep^[(halfLen x).length] (pairB [] x)

private theorem splitHalf_eq (x : List Bool) :
    splitHalf x = pairB (x.take (x.length / 2)) (x.drop (x.length / 2)) := by
  unfold splitHalf
  rw [halfLen_length, takeStep_iter, List.nil_append]

private theorem cpt_splitHalf : CPT splitHalf :=
  cptU (cpt_iterGrow cpt_takeStep 3 takeStep_len cpt_halfLen (cpt_pairB2 (cpt_const []) cpt_id))
    (fun _ => rfl)

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

private def sqToPal (x : List Bool) : List Bool :=
  let sp := splitHalf x
  sel (eqFlag (unpairB sp).1 (unpairB sp).2) [true, false] []

private theorem cpt_sqToPal : CPT sqToPal := by
  have hU := cpt_unpairB1_1 cpt_splitHalf
  have hV := cpt_unpairB2_1 cpt_splitHalf
  exact cptU (cpt_sel (cpt_eqFlag hU hV) (cpt_const [true, false]) (cpt_const [])) (fun _ => rfl)

theorem square_karp_pal_main :
    PvsNP.KarpReducible ({x : List Bool | ∃ y : List Bool, x = y ++ y} : Language Bool)
      ({x : List Bool | x.reverse = x} : Language Bool) := by
  refine ⟨sqToPal, cpt_sqToPal, fun x => ?_⟩
  show (∃ y : List Bool, x = y ++ y) ↔ (sqToPal x).reverse = sqToPal x
  simp only [sqToPal, splitHalf_eq, unpairB_pairB]
  by_cases hsq : x.take (x.length / 2) = x.drop (x.length / 2)
  · have hne : eqFlag (x.take (x.length / 2)) (x.drop (x.length / 2)) ≠ [] :=
      (eqFlag_ne_nil_iff _ _).mpr hsq
    simp only [sel, hne, ↓reduceIte, List.reverse_nil, iff_true]
    refine ⟨x.take (x.length / 2), ?_⟩
    conv_lhs => rw [← List.take_append_drop (x.length / 2) x, ← hsq]
  · have heq : eqFlag (x.take (x.length / 2)) (x.drop (x.length / 2)) = [] := by
      by_contra hne
      exact hsq ((eqFlag_ne_nil_iff _ _).mp hne)
    simp only [sel, heq, ↓reduceIte]
    have hnotpal : ([true, false].reverse = [true, false]) ↔ False := by decide
    rw [hnotpal, iff_false]
    rintro ⟨y, rfl⟩
    apply hsq
    have hlen : (y ++ y).length / 2 = y.length := by
      rw [List.length_append]
      omega
    rw [hlen, List.take_left, List.drop_left]

end PvsNP.Units.m2_x_square_karp_pal

theorem PvsNP.Units.m2_x_square_karp_pal :
    PvsNP.KarpReducible ({x : List Bool | ∃ y : List Bool, x = y ++ y} : Language Bool)
      ({x : List Bool | x.reverse = x} : Language Bool) :=
  PvsNP.Units.m2_x_square_karp_pal.square_karp_pal_main
