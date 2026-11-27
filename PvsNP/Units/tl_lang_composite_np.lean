import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_bool_combine_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_p_rotate_closed
import PvsNP.Units.m2_dfa_in_p

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_composite_np

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-! ### Part 1: Binary values, stripping trailing falses, and `1 < val s` -/

def val (x : List Bool) : ℕ := Nat.ofDigits 2 (x.map Bool.toNat)

theorem val_nil : val [] = 0 := rfl

theorem val_cons (b : Bool) (xs : List Bool) :
    val (b :: xs) = b.toNat + 2 * val xs := by
  simp [val, Nat.ofDigits]

theorem val_append_false (x : List Bool) : val (x ++ [false]) = val x := by
  induction x with
  | nil => simp [val]
  | cons b xs ih => simp [val_cons, ih]

theorem val_lt_two_pow (x : List Bool) : val x < 2 ^ x.length := by
  induction x with
  | nil => simp [val]
  | cons b xs ih =>
    rw [val_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero => simp [val]
  | bit b n ih =>
    by_cases h : n = 0 ∧ b = false
    · rcases h with ⟨rfl, rfl⟩; simp [val]
    · have hcond : n = 0 → b = true := by
        intro hn; cases b <;> simp_all
      rw [Nat.bits_append_bit n b hcond, val_cons, ih, Nat.bit_val]
      omega

theorem bits_length_le_of_lt_two_pow {n k : ℕ} (h : n < 2 ^ k) : (Nat.bits n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    have hn : n = 0 := by simp at h; omega
    subst hn; simp
  | succ k ih =>
    cases n using Nat.binaryRec with
    | zero => simp
    | bit b m =>
      by_cases hm : m = 0 ∧ b = false
      · rcases hm with ⟨rfl, rfl⟩; simp
      · have hcond : m = 0 → b = true := by intro h0; cases b <;> simp_all
        rw [Nat.bits_append_bit m b hcond, List.length_cons]
        rw [Nat.bit_val, pow_succ] at h
        have hm_lt : m < 2 ^ k := by cases b <;> simp at h <;> omega
        have := ih hm_lt
        omega

theorem one_lt_val_iff (s : List Bool) : 1 < val s ↔ s.tail.any id = true := by
  cases s with
  | nil => simp [val]
  | cons b xs =>
    rw [val_cons, List.tail_cons]
    have hpos : 0 < val xs ↔ xs.any id = true := by
      induction xs with
      | nil => simp [val]
      | cons c ys ih =>
        rw [val_cons, List.any_cons, Bool.or_eq_true]
        cases c <;> simp [ih]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.zero_add, ← hpos] <;> omega

def dropFδ : Bool → Bool → Bool × Option Bool
  | false, false => (false, none)
  | false, true => (true, some true)
  | true, b => (true, some b)

def dropFF : Bool → List Bool → List Bool
  | false, l => l.dropWhile (!·)
  | true, l => l

theorem cpt_dropLeadingFalse :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.dropWhile (!·)) := by
  refine PvsNP.Units.m2_transducer_polytime Bool dropFδ (fun _ => none) dropFF ?_ ?_ false
  · intro q; cases q <;> rfl
  · intro q b x; cases q <;> cases b <;> simp [dropFδ, dropFF]

def stripTrail (x : List Bool) : List Bool := (x.reverse.dropWhile (!·)).reverse

theorem cpt_stripTrail :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString stripTrail := by
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.reverse.dropWhile (!·)) :=
    cpt_comp (f := fun x : List Bool => x.reverse) (g := fun x : List Bool => x.dropWhile (!·))
      PvsNP.Units.m2_reverse_polytime cpt_dropLeadingFalse
  exact cpt_comp (f := fun x : List Bool => x.reverse.dropWhile (!·)) (g := fun x : List Bool => x.reverse)
    h1 PvsNP.Units.m2_reverse_polytime

theorem val_stripTrail (x : List Bool) : val (stripTrail x) = val x := by
  have h : ∀ l : List Bool, val (l.dropWhile (!·)).reverse = val l.reverse := by
    intro l
    induction l with
    | nil => rfl
    | cons b l ih =>
      cases b with
      | false =>
        simp only [List.dropWhile_cons, Bool.not_false, ↓reduceIte, List.reverse_cons]
        rw [val_append_false]; exact ih
      | true => simp
  simpa [stripTrail, List.reverse_reverse] using h x.reverse

theorem stripTrail_no_trailing_false (x : List Bool) :
    ∀ h : stripTrail x ≠ [], (stripTrail x).getLast h = true := by
  intro h
  have hrevNe : x.reverse.dropWhile (!·) ≠ [] := by
    intro heq; apply h; rw [stripTrail, heq]; rfl
  have hhead : (x.reverse.dropWhile (!·)).head hrevNe = true := by
    have hprop := List.head_dropWhile_not (p := (!·)) (l := x.reverse) hrevNe
    cases hb : (x.reverse.dropWhile (!·)).head hrevNe
    · rw [hb] at hprop; simp at hprop
    · rfl
  rw [show (stripTrail x).getLast h = (x.reverse.dropWhile (!·)).head hrevNe by
    simp only [stripTrail, List.getLast_reverse], hhead]

theorem bits_eq_of_val_no_trailing :
    ∀ (y : List Bool), (∀ h : y ≠ [], y.getLast h = true) → Nat.bits (val y) = y := by
  intro y
  induction y with
  | nil => intro _; simp [val]
  | cons b ys ih =>
    intro hlast
    have hysLast : ∀ h : ys ≠ [], ys.getLast h = true := by
      intro h; rw [← List.getLast_cons h]; exact hlast (List.cons_ne_nil b ys)
    have hih := ih hysLast
    have hcond : val ys = 0 → b = true := by
      intro hz
      cases ys with
      | nil => simpa using hlast (List.cons_ne_nil b [])
      | cons c cs => rw [hz] at hih; simp at hih
    rw [val_cons, Nat.add_comm, ← Nat.bit_val, Nat.bits_append_bit (val ys) b hcond, hih]

theorem stripTrail_eq_iff (u v : List Bool) : stripTrail u = stripTrail v ↔ val u = val v := by
  have hu : Nat.bits (val u) = stripTrail u := by
    rw [← val_stripTrail u]
    exact bits_eq_of_val_no_trailing (stripTrail u) (stripTrail_no_trailing_false u)
  have hv : Nat.bits (val v) = stripTrail v := by
    rw [← val_stripTrail v]
    exact bits_eq_of_val_no_trailing (stripTrail v) (stripTrail_no_trailing_false v)
  constructor
  · intro h; rw [← val_stripTrail u, ← val_stripTrail v, h]
  · intro h; rw [← hu, ← hv, h]

theorem cpt_any_id :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun x : List Bool => x.any id) := by
  have h := PvsNP.Units.m2_dfa_in_p.dfa_polyTime (fun q b : Bool => q || b) false id
  have heq : (fun x : List Bool => id (x.foldl (fun q b => q || b) false)) =
      (fun x : List Bool => x.any id) := by
    funext x
    have hfold : ∀ (q : Bool) (l : List Bool), l.foldl (fun a b => a || b) q = (q || l.any id) := by
      intro q l
      induction l generalizing q with
      | nil => simp
      | cons b l ih => simp [ih, Bool.or_assoc]
    simpa using hfold false x
  rwa [heq] at h

theorem cpt_zeroPad :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.map (fun _ => false)) := by
  refine PvsNP.Units.m2_transducer_polytime Unit (fun _ _ => ((), some false)) (fun _ => none)
    (fun _ l => l.map (fun _ => false)) ?_ ?_ ()
  · intro _; rfl
  · intro _ _ _; simp

/-! ### Part 2: Polytime fixed-width binary addition `addFixed (u, v)` -/

theorem unpairB_weighted (u : List Bool) :
    2 * (unpairB u).1.length + (unpairB u).2.length ≤ u.length := by
  have h1 : (unpairB u).1.length ≤ (u.takeWhile id).length := by simp [unpairB]
  have h2 : (unpairB u).1.length + (unpairB u).2.length ≤ (u.dropWhile id).length := by
    simp only [unpairB]
    have htd := List.take_append_drop (u.takeWhile id).length (u.dropWhile id).tail
    have hl := congrArg List.length htd
    simp only [List.length_append, List.length_tail] at hl
    omega
  have h3 : (u.takeWhile id).length + (u.dropWhile id).length = u.length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  omega

def apack (c : Bool) (u v outRev : List Bool) : List Bool :=
  pairB [c] (pairB (pairB u v) outRev)

def aC (s : List Bool) : Bool := decide ((unpairB s).1 = [true])
def aUV (s : List Bool) : List Bool := (unpairB (unpairB s).2).1
def aOut (s : List Bool) : List Bool := (unpairB (unpairB s).2).2
def aU (s : List Bool) : List Bool := (unpairB (aUV s)).1
def aV (s : List Bool) : List Bool := (unpairB (aUV s)).2

def addStep (s : List Bool) : List Bool :=
  let b1 := decide ((aU s).take 1 = [true])
  let b2 := decide ((aV s).take 1 = [true])
  let c := aC s
  let sb := (b1 != b2) != c
  let c' := (b1 && b2) || (c && (b1 || b2))
  apack c' (aU s).tail (aV s).tail (sb :: aOut s)

theorem addStep_len (s : List Bool) : (addStep s).length ≤ s.length + 7 := by
  unfold addStep apack
  simp only [pairB_length, List.length_cons, List.length_nil]
  have h0 := unpairB_weighted s
  have h1 := unpairB_weighted (unpairB s).2
  have h2 := unpairB_weighted (aUV s)
  change 2 * (aUV s).length + (aOut s).length ≤ (unpairB s).2.length at h1
  change 2 * (aU s).length + (aV s).length ≤ (aUV s).length at h2
  have hu : (aU s).tail.length ≤ (aU s).length := by rw [List.length_tail]; omega
  have hv : (aV s).tail.length ≤ (aV s).length := by rw [List.length_tail]; omega
  omega

theorem cpt_bool_eq_const (c : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => decide (x = c)) :=
  cpt_comp (PvsNP.Units.m2_pair_build_polytime _ _ cpt_id (cpt_const c))
    PvsNP.Units.m2_eq_polytime

theorem cpt_bool_to_bit {c : List Bool → Bool}
    (hc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer c) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => [c s]) := by
  have h := PvsNP.Units.m2_ite_polytime c (fun _ => [true]) (fun _ => [false])
    hc (cpt_const [true]) (cpt_const [false])
  have heq : (fun s : List Bool => if c s = true then [true] else [false]) = (fun s => [c s]) := by
    funext s; cases c s <;> rfl
  rwa [heq] at h

theorem cpt_addStep :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString addStep := by
  have hF : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1_1 cpt_id
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  have hUV : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString aUV := cpt_unpairB1_1 hB
  have hOut : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString aOut := cpt_unpairB2_1 hB
  have hU : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString aU := cpt_unpairB1_1 hUV
  have hV : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString aV := cpt_unpairB2_1 hUV
  have hC : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer aC :=
    cpt_comp (f := fun s => (unpairB s).1) (g := fun x => decide (x = [true]))
      hF (cpt_bool_eq_const [true])
  have hb1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide ((aU s).take 1 = [true])) :=
    cpt_comp (cpt_comp hU PvsNP.Units.m2_p_rotate_closed.cpt_take1) (cpt_bool_eq_const [true])
  have hb2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide ((aV s).take 1 = [true])) :=
    cpt_comp (cpt_comp hV PvsNP.Units.m2_p_rotate_closed.cpt_take1) (cpt_bool_eq_const [true])
  have hxor := PvsNP.Units.m2_bool_combine_polytime (· != ·) _ _ hb1 hb2
  have hsb := PvsNP.Units.m2_bool_combine_polytime (· != ·) _ _ hxor hC
  have hand := PvsNP.Units.m2_bool_combine_polytime (· && ·) _ _ hb1 hb2
  have hor := PvsNP.Units.m2_bool_combine_polytime (· || ·) _ _ hb1 hb2
  have hcor := PvsNP.Units.m2_bool_combine_polytime (· && ·) _ _ hC hor
  have hc' := PvsNP.Units.m2_bool_combine_polytime (· || ·) _ _ hand hcor
  have hOut' : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (((decide ((aU s).take 1 = [true]) != decide ((aV s).take 1 = [true])) != aC s)) :: aOut s) := by
    have h := cpt_app2 (cpt_bool_to_bit hsb) hOut
    have heq : (fun s => [((decide ((aU s).take 1 = [true]) != decide ((aV s).take 1 = [true])) != aC s)] ++ aOut s) =
        (fun s => (((decide ((aU s).take 1 = [true]) != decide ((aV s).take 1 = [true])) != aC s)) :: aOut s) := rfl
    rwa [heq] at h
  exact cpt_pairB2 (cpt_bool_to_bit hc') (cpt_pairB2 (cpt_pairB2 (cpt_tail1 hU) (cpt_tail1 hV)) hOut')

def addBody : Bool → List Bool → List Bool → List Bool
  | _, [], _ => []
  | c, b1 :: u, v =>
      let b2 := v.headD false
      let sb := (b1 != b2) != c
      let c' := (b1 && b2) || (c && (b1 || b2))
      sb :: addBody c' u v.tail

def addCarry : Bool → List Bool → List Bool → Bool
  | c, [], _ => c
  | c, b1 :: u, v =>
      let b2 := v.headD false
      let c' := (b1 && b2) || (c && (b1 || b2))
      addCarry c' u v.tail

theorem addStep_iter :
    ∀ (u v outRev : List Bool) (c : Bool),
      addStep^[u.length] (apack c u v outRev) =
        apack (addCarry c u v) [] (v.drop u.length) ((addBody c u v).reverse ++ outRev) := by
  intro u
  induction u with
  | nil => intro v outRev c; simp [addCarry, addBody]
  | cons b1 u ih =>
    intro v outRev c
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : addStep (apack c (b1 :: u) v outRev) =
        apack ((b1 && v.headD false) || (c && (b1 || v.headD false))) u v.tail
          (((b1 != v.headD false) != c) :: outRev) := by
      have hb1 : decide ((b1 :: u).take 1 = [true]) = b1 := by cases b1 <;> rfl
      have hb2 : decide (v.take 1 = [true]) = v.headD false := by
        cases v with
        | nil => rfl
        | cons b2 _ => cases b2 <;> rfl
      have hc : decide ([c] = [true]) = c := by cases c <;> rfl
      simp only [addStep, apack, aC, aUV, aOut, aU, aV, unpairB_pairB, hb1, hb2, hc, List.tail_cons]
    rw [h1, ih v.tail _ _]
    have hdrop : v.tail.drop u.length = v.drop (u.length + 1) := by
      cases v <;> simp
    simp only [addCarry, addBody, hdrop, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append]

theorem addBody_length (c : Bool) (u v : List Bool) : (addBody c u v).length = u.length := by
  induction u generalizing c v with
  | nil => rfl
  | cons b1 u ih => simp [addBody, ih]

theorem addBits_val :
    ∀ (u v : List Bool) (c : Bool), v.length ≤ u.length →
      val (addBody c u v ++ [addCarry c u v]) = val u + val v + c.toNat := by
  intro u
  induction u with
  | nil =>
    intro v c hle
    cases v with
    | nil => cases c <;> simp [addBody, addCarry, val]
    | cons _ _ => simp at hle
  | cons b1 u ih =>
    intro v c hle
    cases v with
    | nil =>
      simp only [addBody, addCarry, List.headD_nil, List.tail_nil, List.cons_append, val_cons, val_nil]
      have hrec := ih [] ((b1 && false) || (c && (b1 || false))) (by simp)
      rw [hrec, val_nil]
      cases b1 <;> cases c <;> simp <;> omega
    | cons b2 v =>
      simp only [addBody, addCarry, List.headD_cons, List.tail_cons, List.cons_append, val_cons]
      have hrec := ih v ((b1 && b2) || (c && (b1 || b2))) (by simpa using hle)
      rw [hrec]
      cases b1 <;> cases b2 <;> cases c <;> simp <;> omega

def addFixed (s : List Bool) : List Bool :=
  let u := (unpairB s).1
  let v := (unpairB s).2
  let fin := addStep^[u.length] (apack false u v [])
  (aOut fin).reverse ++ [aC fin]

theorem addFixed_pairB (u v : List Bool) :
    addFixed (pairB u v) = addBody false u v ++ [addCarry false u v] := by
  unfold addFixed
  simp only [unpairB_pairB, addStep_iter, List.append_nil]
  have hc : decide ([addCarry false u v] = [true]) = addCarry false u v := by
    cases addCarry false u v <;> rfl
  simp only [apack, aOut, aC, unpairB_pairB, List.reverse_reverse, hc]

theorem addFixed_length (u v : List Bool) :
    (addFixed (pairB u v)).length = u.length + 1 := by
  rw [addFixed_pairB, List.length_append, addBody_length, List.length_singleton]

theorem cpt_addFixed :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString addFixed := by
  have hu : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1_1 cpt_id
  have hv : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  have hInit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => apack false (unpairB s).1 (unpairB s).2 []) :=
    cpt_pairB2 (cpt_const [false]) (cpt_pairB2 (cpt_pairB2 hu hv) (cpt_const []))
  have hIter := PvsNP.Units.m2_iterate_polytime addStep 7 cpt_addStep addStep_len
  have hFin : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => addStep^[(unpairB s).1.length] (apack false (unpairB s).1 (unpairB s).2 [])) :=
    cpt_comp (f := fun s => (apack false (unpairB s).1 (unpairB s).2 [], (unpairB s).1))
      (g := fun p : List Bool × List Bool => addStep^[p.2.length] p.1)
      (PvsNP.Units.m2_pair_build_polytime _ _ hInit hu) hIter
  have hOutRev : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (aOut (addStep^[(unpairB s).1.length] (apack false (unpairB s).1 (unpairB s).2 []))).reverse) :=
    cpt_comp (cpt_unpairB2_1 (cpt_unpairB2_1 hFin)) PvsNP.Units.m2_reverse_polytime
  have hCarryBit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => [aC (addStep^[(unpairB s).1.length] (apack false (unpairB s).1 (unpairB s).2 []))]) :=
    cpt_bool_to_bit (cpt_comp
      (f := fun s => (unpairB (addStep^[(unpairB s).1.length] (apack false (unpairB s).1 (unpairB s).2 []))).1)
      (g := fun x => decide (x = [true]))
      (cpt_unpairB1_1 hFin) (cpt_bool_eq_const [true]))
  exact cpt_app2 hOutRev hCarryBit

/-! ### Part 3: Polytime binary multiplication `binMul` -/

def mpack (A curB acc : List Bool) : List Bool := pairB (pairB A curB) acc

def mLeft (s : List Bool) : List Bool := (unpairB s).1
def mAcc (s : List Bool) : List Bool := (unpairB s).2
def mA (s : List Bool) : List Bool := (unpairB (mLeft s)).1
def mB (s : List Bool) : List Bool := (unpairB (mLeft s)).2

def mulStep (s : List Bool) : List Bool :=
  if !(decide (mA s = [])) then
    let acc' := if decide ((mA s).take 1 = [true]) then addFixed (pairB (mAcc s) (mB s)) else mAcc s ++ [false]
    mpack (mA s).tail (false :: mB s) acc'
  else s

theorem mulStep_len (s : List Bool) : (mulStep s).length ≤ s.length + 3 := by
  unfold mulStep
  split_ifs with hne hbit
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hne
    have hApos : 1 ≤ (mA s).length := List.length_pos_iff.mpr hne
    have h0 := unpairB_weighted s
    have h1 := unpairB_weighted (mLeft s)
    change 2 * (mLeft s).length + (mAcc s).length ≤ s.length at h0
    change 2 * (mA s).length + (mB s).length ≤ (mLeft s).length at h1
    simp only [mpack, pairB_length, List.length_tail, List.length_cons, addFixed_length]
    omega
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hne
    have hApos : 1 ≤ (mA s).length := List.length_pos_iff.mpr hne
    have h0 := unpairB_weighted s
    have h1 := unpairB_weighted (mLeft s)
    change 2 * (mLeft s).length + (mAcc s).length ≤ s.length at h0
    change 2 * (mA s).length + (mB s).length ≤ (mLeft s).length at h1
    simp only [mpack, pairB_length, List.length_tail, List.length_cons, List.length_append,
      List.length_nil]
    omega
  · omega

theorem cpt_mulStep :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString mulStep := by
  have hL : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString mLeft := cpt_unpairB1_1 cpt_id
  have hAcc : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString mAcc := cpt_unpairB2_1 cpt_id
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString mA := cpt_unpairB1_1 hL
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString mB := cpt_unpairB2_1 hL
  have hne : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun s => !(decide (mA s = []))) :=
    PvsNP.Units.m2_bool_combine_polytime (fun a _ => !a) _ _
      (cpt_comp hA (cpt_bool_eq_const [])) (cpt_comp hA (cpt_bool_eq_const []))
  have hbit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide ((mA s).take 1 = [true])) :=
    cpt_comp (cpt_comp hA PvsNP.Units.m2_p_rotate_closed.cpt_take1) (cpt_bool_eq_const [true])
  have hAdd : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => addFixed (pairB (mAcc s) (mB s))) :=
    cpt_comp (cpt_pairB2 hAcc hB) cpt_addFixed
  have hPad : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => mAcc s ++ [false]) :=
    cpt_app2 hAcc (cpt_const [false])
  have hAcc' := PvsNP.Units.m2_ite_polytime _ _ _ hbit hAdd hPad
  have hB' : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => false :: mB s) := by
    have h := cpt_app2 (cpt_const [false]) hB
    have heq : (fun s => [false] ++ mB s) = (fun s => false :: mB s) := rfl
    rwa [heq] at h
  have hBranch := cpt_pairB2 (cpt_pairB2 (cpt_tail1 hA) hB') hAcc'
  exact PvsNP.Units.m2_ite_polytime _ _ _ hne hBranch cpt_id

theorem mulStep_iter_val :
    ∀ (A curB acc : List Bool), curB.length ≤ acc.length →
      val (mAcc (mulStep^[A.length] (mpack A curB acc))) = val acc + val A * val curB := by
  intro A
  induction A with
  | nil =>
    intro curB acc _
    simp [mAcc, mpack, unpairB_pairB, val_nil]
  | cons a A ih =>
    intro curB acc hle
    rw [List.length_cons, Function.iterate_succ_apply]
    cases a with
    | false =>
      have h1 : mulStep (mpack (false :: A) curB acc) = mpack A (false :: curB) (acc ++ [false]) := by
        simp [mulStep, mpack, mLeft, mA, mB, mAcc, unpairB_pairB]
      rw [h1, ih (false :: curB) (acc ++ [false]) (by simp; omega)]
      rw [val_append_false, val_cons, val_cons]
      simp only [Bool.toNat_false, Nat.zero_add]
      ring
    | true =>
      have h1 : mulStep (mpack (true :: A) curB acc) =
          mpack A (false :: curB) (addFixed (pairB acc curB)) := by
        simp [mulStep, mpack, mLeft, mA, mB, mAcc, unpairB_pairB]
      rw [h1, ih (false :: curB) (addFixed (pairB acc curB)) (by rw [addFixed_length]; simp; omega)]
      rw [addFixed_pairB, addBits_val acc curB false hle, val_cons, val_cons]
      simp only [Bool.toNat_true, Bool.toNat_false, Nat.add_zero, Nat.zero_add]
      ring

def binMul (s : List Bool) : List Bool :=
  let A := (unpairB s).1
  let B := (unpairB s).2
  mAcc (mulStep^[A.length] (mpack A B (B.map (fun _ => false))))

theorem binMul_val (A B : List Bool) : val (binMul (pairB A B)) = val A * val B := by
  unfold binMul
  simp only [unpairB_pairB]
  have hle : B.length ≤ (B.map (fun _ => false)).length := by simp
  rw [mulStep_iter_val A B (B.map (fun _ => false)) hle]
  have h0 : ∀ l : List Bool, val (l.map (fun _ => false)) = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons _ bs ih =>
      simp only [List.map_cons, val_cons, Bool.toNat_false, ih]
  rw [h0 B, Nat.zero_add]

theorem cpt_binMul :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString binMul := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1_1 cpt_id
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  have hAcc0 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).2.map (fun _ => false)) :=
    cpt_comp hB cpt_zeroPad
  have hInit := cpt_pairB2 (cpt_pairB2 hA hB) hAcc0
  have hIter := PvsNP.Units.m2_iterate_polytime mulStep 3 cpt_mulStep mulStep_len
  have hRun : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => mulStep^[(unpairB s).1.length] (mpack (unpairB s).1 (unpairB s).2 ((unpairB s).2.map (fun _ => false)))) :=
    cpt_comp (f := fun s => (mpack (unpairB s).1 (unpairB s).2 ((unpairB s).2.map (fun _ => false)), (unpairB s).1))
      (g := fun p : List Bool × List Bool => mulStep^[p.2.length] p.1)
      (PvsNP.Units.m2_pair_build_polytime _ _ hInit hA) hIter
  exact cpt_unpairB2_1 hRun

/-! ### Part 4: NP verifier for composite binary numerals -/

def compVerStr (s : List Bool) : Bool :=
  let x := (unpairB s).1
  let cert := (unpairB s).2
  let A := (unpairB cert).1
  let B := (unpairB cert).2
  A.tail.any id && B.tail.any id && decide (stripTrail (binMul cert) = stripTrail x)

def compVerifier (p : List Bool × List Bool) : Bool :=
  compVerStr (pairB p.1 p.2)

theorem cpt_compVerifier :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer compVerifier := by
  have hX : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1_1 cpt_id
  have hCert : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB (unpairB s).2).1) :=
    cpt_unpairB1_1 hCert
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB (unpairB s).2).2) :=
    cpt_unpairB2_1 hCert
  have hg1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => (unpairB (unpairB s).2).1.tail.any id) :=
    cpt_comp (cpt_tail1 hA) cpt_any_id
  have hg2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => (unpairB (unpairB s).2).2.tail.any id) :=
    cpt_comp (cpt_tail1 hB) cpt_any_id
  have hProd : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => stripTrail (binMul (unpairB s).2)) :=
    cpt_comp (cpt_comp hCert cpt_binMul) cpt_stripTrail
  have hXstrip : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => stripTrail (unpairB s).1) :=
    cpt_comp hX cpt_stripTrail
  have hEq : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide (stripTrail (binMul (unpairB s).2) = stripTrail (unpairB s).1)) :=
    cpt_comp (PvsNP.Units.m2_pair_build_polytime _ _ hProd hXstrip) PvsNP.Units.m2_eq_polytime
  have hStr : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer compVerStr :=
    PvsNP.Units.m2_bool_combine_polytime (· && ·) _ _
      (PvsNP.Units.m2_bool_combine_polytime (· && ·) _ _ hg1 hg2) hEq
  exact cpt_comp (f := fun p : List Bool × List Bool => pairB p.1 p.2) (g := compVerStr)
    cpt_pairB hStr

end PvsNP.Units.tl_lang_composite_np

/-- The strings whose binary value is composite are in NP (TM2): witness `pairB (Nat.bits a) (Nat.bits b)`
    verified by polynomial-time binary multiplication. -/
theorem PvsNP.Units.tl_lang_composite_np :
    ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.NP := by
  refine ⟨PvsNP.Units.tl_lang_composite_np.compVerifier, Polynomial.C 3 * Polynomial.X + Polynomial.C 1,
    PvsNP.Units.tl_lang_composite_np.cpt_compVerifier, fun x => ?_⟩
  change (∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = PvsNP.Units.tl_lang_composite_np.val x) ↔
    ∃ w : List Bool, w.length ≤ (Polynomial.C 3 * Polynomial.X + Polynomial.C 1).eval x.length ∧
      PvsNP.Units.tl_lang_composite_np.compVerifier (x, w) = true
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    let A := Nat.bits a
    let B := Nat.bits b
    let w := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB A B
    have hlt := PvsNP.Units.tl_lang_composite_np.val_lt_two_pow x
    have ha_lt : a < 2 ^ x.length := by
      have : a ≤ a * b := Nat.le_mul_of_pos_right a (by omega)
      omega
    have hb_lt : b < 2 ^ x.length := by
      have : b ≤ a * b := Nat.le_mul_of_pos_left b (by omega)
      omega
    have hAlen : A.length ≤ x.length := PvsNP.Units.tl_lang_composite_np.bits_length_le_of_lt_two_pow ha_lt
    have hBlen : B.length ≤ x.length := PvsNP.Units.tl_lang_composite_np.bits_length_le_of_lt_two_pow hb_lt
    refine ⟨w, ?_, ?_⟩
    · simp only [w, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB_length,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      omega
    · simp only [w, A, B, PvsNP.Units.tl_lang_composite_np.compVerifier,
        PvsNP.Units.tl_lang_composite_np.compVerStr,
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB,
        Bool.and_eq_true, decide_eq_true_eq,
        PvsNP.Units.tl_lang_composite_np.stripTrail_eq_iff,
        PvsNP.Units.tl_lang_composite_np.binMul_val]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← PvsNP.Units.tl_lang_composite_np.one_lt_val_iff, PvsNP.Units.tl_lang_composite_np.val_bits]
        exact ha
      · rw [← PvsNP.Units.tl_lang_composite_np.one_lt_val_iff, PvsNP.Units.tl_lang_composite_np.val_bits]
        exact hb
      · rw [PvsNP.Units.tl_lang_composite_np.val_bits, PvsNP.Units.tl_lang_composite_np.val_bits]
        exact hab
  · rintro ⟨w, _, hacc⟩
    simp only [PvsNP.Units.tl_lang_composite_np.compVerifier,
      PvsNP.Units.tl_lang_composite_np.compVerStr,
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB,
      Bool.and_eq_true, decide_eq_true_eq,
      PvsNP.Units.tl_lang_composite_np.stripTrail_eq_iff] at hacc
    set A := (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB w).1
    set B := (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB w).2
    refine ⟨PvsNP.Units.tl_lang_composite_np.val A, PvsNP.Units.tl_lang_composite_np.val B,
      (PvsNP.Units.tl_lang_composite_np.one_lt_val_iff A).2 hacc.1.1,
      (PvsNP.Units.tl_lang_composite_np.one_lt_val_iff B).2 hacc.1.2, ?_⟩
    have hmul := PvsNP.Units.tl_lang_composite_np.binMul_val A B
    -- Wait: binMul w vs binMul (pairB A B)!
    -- Look! binMul only reads `(unpairB w).1` and `(unpairB w).2`, which ARE `A` and `B`!
    have heq : PvsNP.Units.tl_lang_composite_np.binMul w =
        PvsNP.Units.tl_lang_composite_np.binMul (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB A B) := by
      simp [PvsNP.Units.tl_lang_composite_np.binMul, A, B,
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB]
    rw [← hmul, ← heq]
    exact hacc.2
