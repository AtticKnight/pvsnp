import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.tf_fun_pair_add
import PvsNP.Units.tf_fun_pair_mul
import PvsNP.Units.m2_bounded_unary_search_polytime

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_val_perfect_power_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

abbrev CPT (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f

private theorem encodePair_eq :
    PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
  funext ⟨_, _⟩
  rfl

private theorem pp_cptE {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f f' : α → β} (h : ComputableInPolyTime ea eb f) (e : ∀ a, f a = f' a) :
    ComputableInPolyTime ea eb f' := by
  obtain rfl : f = f' := funext e
  exact h

def val (l : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (l.map Bool.toNat)

theorem val_nil : val [] = 0 := rfl

theorem val_cons (b : Bool) (l : List Bool) :
    val (b :: l) = b.toNat + 2 * val l := by
  simp only [val, List.map_cons, Nat.ofDigits_cons]

theorem val_lt_two_pow (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil =>
    simp only [val_nil, List.length_nil, Nat.pow_zero]
    decide
  | cons b rest ih =>
    rw [val_cons, List.length_cons, Nat.pow_succ]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero =>
    simp only [Nat.zero_bits, val_nil]
  | bit b m ih =>
    by_cases h : b = false ∧ m = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp only [Nat.bit_false, Nat.mul_zero, Nat.zero_bits, val_nil]
    · have hne : m = 0 → b = true := by
        intro hm
        cases b
        · exact absurd ⟨rfl, hm⟩ h
        · rfl
      rw [Nat.bits_append_bit m b hne, val_cons, ih]
      cases b
      · simp only [Nat.bit_false, Bool.toNat_false]; omega
      · simp only [Nat.bit_true, Bool.toNat_true]; omega

theorem length_bits_le (k : ℕ) : ∀ n : ℕ, n < 2 ^ k → (Nat.bits n).length ≤ k := by
  induction k with
  | zero =>
    intro n hn
    have h0 : n = 0 := by simp only [Nat.pow_zero] at hn; omega
    subst h0
    simp only [Nat.zero_bits, List.length_nil, le_refl]
  | succ k ih =>
    intro n hn
    induction n using Nat.binaryRec with
    | zero =>
      simp only [Nat.zero_bits, List.length_nil, Nat.zero_le]
    | bit b m _ =>
      by_cases h : b = false ∧ m = 0
      · obtain ⟨rfl, rfl⟩ := h
        simp only [Nat.bit_false, Nat.mul_zero, Nat.zero_bits, List.length_nil, Nat.zero_le]
      · have hne : m = 0 → b = true := by
          intro hm
          cases b
          · exact absurd ⟨rfl, hm⟩ h
          · rfl
        rw [Nat.bits_append_bit m b hne, List.length_cons]
        have hm : m < 2 ^ k := by
          rw [Nat.pow_succ] at hn
          cases b
          · simp only [Nat.bit_false] at hn; omega
          · simp only [Nat.bit_true] at hn; omega
        have hlen := ih m hm
        omega

def pow2List (k : ℕ) : List Bool :=
  List.replicate k false ++ [true]

theorem val_pow2List (k : ℕ) : val (pow2List k) = 2 ^ k := by
  induction k with
  | zero =>
    simp only [pow2List, List.replicate_zero, List.nil_append, val_cons, val_nil,
      Bool.toNat_true, Nat.mul_zero, Nat.add_zero, Nat.pow_zero]
  | succ k ih =>
    simp only [pow2List, List.replicate_succ, List.cons_append, val_cons, Bool.toNat_false,
      Nat.zero_add] at ih ⊢
    rw [ih, Nat.pow_succ, Nat.mul_comm]

theorem pow2List_length (k : ℕ) : (pow2List k).length = k + 1 := by
  simp only [pow2List, List.length_append, List.length_replicate, List.length_cons, List.length_nil]

theorem cpt_zeros : CPT (fun x : List Bool => List.replicate x.length false) := by
  refine filterMap_polyTime _ _ _ (fun _ : Bool => some false) ?_
  intro x
  induction x with
  | nil => rfl
  | cons _ rest ih =>
    simp only [List.length_cons, List.replicate_succ, List.filterMap_cons] at ih ⊢
    exact congrArg (List.cons false) ih

theorem cpt_pow2 : CPT (fun x : List Bool => pow2List x.length) :=
  pp_cptE (cpt_app2 cpt_zeros (cpt_const [true])) (fun _ => rfl)

private theorem cpt_add :
    ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => Nat.bits (val p.1 + val p.2)) := by
  rw [← encodePair_eq]
  exact PvsNP.Units.tf_fun_pair_add

private theorem cpt_mul :
    ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2)) := by
  rw [← encodePair_eq]
  exact PvsNP.Units.tf_fun_pair_mul

private theorem cpt_ble :
    ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2)) := by
  rw [← encodePair_eq]
  exact PvsNP.Units.m2_binary_le_polytime

-- Part A: Capped exponentiation powCap x a u
-- State: pairB (pairB x a) cur
def pX (s : List Bool) : List Bool := (unpairB (unpairB s).1).1
def pA (s : List Bool) : List Bool := (unpairB (unpairB s).1).2
def pCur (s : List Bool) : List Bool := (unpairB s).2

def powStep (s : List Bool) : List Bool :=
  let x := pX s
  let a := pA s
  let cur := pCur s
  let prod := Nat.bits (val cur * val a)
  let ok := if decide (val prod ≤ val x) then [true] else []
  pairB (pairB x a) (sel ok (pow2List x.length) prod)

def powMeasure (s : List Bool) : ℕ := (pX s).length + 4

theorem powMeasure_step (s : List Bool) : powMeasure (powStep s) ≤ powMeasure s := by
  simp only [powMeasure, powStep, pX, unpairB_pairB, le_refl]

theorem powMeasure_linear (s : List Bool) : powMeasure s ≤ 4 * s.length + 4 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  unfold powMeasure pX
  omega

theorem powStep_len (s : List Bool) : (powStep s).length ≤ s.length + powMeasure s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  have hbound : 4 * (pX s).length + 2 * (pA s).length + (pCur s).length ≤ s.length := by
    unfold pX pA pCur
    omega
  unfold powStep powMeasure
  dsimp only
  rw [pairB_length, pairB_length]
  by_cases hok : val (Nat.bits (val (pCur s) * val (pA s))) ≤ val (pX s)
  · have hflag : (if decide (val (Nat.bits (val (pCur s) * val (pA s))) ≤ val (pX s)) then [true] else []) = [true] := by
      simp only [hok, decide_true, ↓reduceIte]
    rw [hflag, sel_cons]
    have hlt : val (pCur s) * val (pA s) < 2 ^ (pX s).length := by
      have hx := val_lt_two_pow (pX s)
      rw [val_bits] at hok
      omega
    have hblen := length_bits_le (pX s).length (val (pCur s) * val (pA s)) hlt
    omega
  · have hflag : (if decide (val (Nat.bits (val (pCur s) * val (pA s))) ≤ val (pX s)) then [true] else []) = [] := by
      simp only [hok, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [hflag, sel_nil, pow2List_length]
    omega

theorem cpt_powStep : CPT powStep := by
  have hX : CPT pX := cpt_unpairB1_1 cpt_unpairB1
  have hA : CPT pA := cpt_unpairB2_1 cpt_unpairB1
  have hCur : CPT pCur := cpt_unpairB2
  have hProd : CPT (fun s => Nat.bits (val (pCur s) * val (pA s))) :=
    pp_cptE (cpt_comp (cpt_pair hCur hA) cpt_mul) (fun _ => rfl)
  have hOk := cpt_bitFlag (cpt_comp (cpt_pair hProd hX) cpt_ble)
  have hCap := cpt_comp hX cpt_pow2
  have hNext := cpt_sel hOk hCap hProd
  exact pp_cptE (cpt_pairB2 (cpt_pairB2 hX hA) hNext) (fun _ => rfl)

def powCap (x a u : List Bool) : List Bool :=
  (unpairB (powStep^[u.length] (pairB (pairB x a) [true]))).2

theorem cpt_powCapS : CPT (fun s => powCap (pX s) (pA s) (pCur s)) := by
  have hX : CPT pX := cpt_unpairB1_1 cpt_unpairB1
  have hA : CPT pA := cpt_unpairB2_1 cpt_unpairB1
  have hU : CPT pCur := cpt_unpairB2
  have hInit := cpt_pairB2 (cpt_pairB2 hX hA) (cpt_const [true])
  obtain ⟨cPow⟩ := cpt_powStep
  have hIter := Iter.iter_polyTime_measure powStep cPow powMeasure 4
    powMeasure_step powStep_len powMeasure_linear
  exact pp_cptE (cpt_unpairB2_1 (cpt_comp (cpt_pair hInit hU) hIter)) (fun _ => rfl)

theorem powStep_iter_fst (x a : List Bool) (k : ℕ) :
    ∃ res : List Bool, powStep^[k] (pairB (pairB x a) [true]) = pairB (pairB x a) res := by
  induction k with
  | zero =>
    exact ⟨[true], rfl⟩
  | succ k ih =>
    obtain ⟨res, hres⟩ := ih
    rw [Function.iterate_succ_apply', hres]
    unfold powStep
    simp only [pX, pA, pCur, unpairB_pairB]
    exact ⟨_, rfl⟩

theorem powStep_iter_pos (x a : List Bool) (ha : 1 ≤ val a) (k : ℕ) :
    ∃ res : List Bool,
      powStep^[k] (pairB (pairB x a) [true]) = pairB (pairB x a) res ∧
      (val res ≤ val x ↔ val a ^ k ≤ val x) ∧
      (val a ^ k ≤ val x → val res = val a ^ k) := by
  induction k with
  | zero =>
    refine ⟨[true], rfl, ?_, ?_⟩
    · simp only [val_cons, val_nil, Bool.toNat_true, Nat.mul_zero, Nat.add_zero, Nat.pow_zero]
    · intro _
      simp only [val_cons, val_nil, Bool.toNat_true, Nat.mul_zero, Nat.add_zero, Nat.pow_zero]
  | succ k ih =>
    obtain ⟨res, hres, hiff, heq⟩ := ih
    rw [Function.iterate_succ_apply', hres]
    have hstep : powStep (pairB (pairB x a) res) =
        pairB (pairB x a)
          (sel (if decide (val (Nat.bits (val res * val a)) ≤ val x) then [true] else [])
            (pow2List x.length) (Nat.bits (val res * val a))) := by
      simp only [powStep, pX, pA, pCur, unpairB_pairB]
    rw [hstep]
    refine ⟨_, rfl, ?_, ?_⟩
    · by_cases hk : val a ^ k ≤ val x
      · have hr : val res = val a ^ k := heq hk
        have hvp : val (Nat.bits (val res * val a)) = val a ^ (k + 1) := by
          rw [val_bits, hr, Nat.pow_succ]
        by_cases hk1 : val a ^ (k + 1) ≤ val x
        · have hflag : (if decide (val (Nat.bits (val res * val a)) ≤ val x) then [true] else []) = [true] := by
            rw [hvp]; simp only [hk1, decide_true, ↓reduceIte]
          rw [hflag, sel_cons, hvp]
        · have hflag : (if decide (val (Nat.bits (val res * val a)) ≤ val x) then [true] else []) = [] := by
            rw [hvp]; simp only [hk1, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [hflag, sel_nil, val_pow2List]
          have hxlt := val_lt_two_pow x
          exact ⟨fun h => absurd h (by omega), fun h => absurd h hk1⟩
      · have hrgt : ¬ (val res ≤ val x) := fun h => hk (hiff.mp h)
        have hmul_ge : val res ≤ val res * val a := by
          have := Nat.mul_le_mul_left (val res) ha
          rw [Nat.mul_one] at this
          exact this
        have hpow_ge : val a ^ k ≤ val a ^ (k + 1) := by
          rw [Nat.pow_succ]
          have := Nat.mul_le_mul_left (val a ^ k) ha
          rw [Nat.mul_one] at this
          exact this
        have hnotp : ¬ (val (Nat.bits (val res * val a)) ≤ val x) := by
          rw [val_bits]; omega
        have hnotk1 : ¬ (val a ^ (k + 1) ≤ val x) := by omega
        have hflag : (if decide (val (Nat.bits (val res * val a)) ≤ val x) then [true] else []) = [] := by
          simp only [hnotp, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [hflag, sel_nil, val_pow2List]
        have hxlt := val_lt_two_pow x
        exact ⟨fun h => absurd h (by omega), fun h => absurd h hnotk1⟩
    · intro hk1
      have hpow_ge : val a ^ k ≤ val a ^ (k + 1) := by
        rw [Nat.pow_succ]
        have := Nat.mul_le_mul_left (val a ^ k) ha
        rw [Nat.mul_one] at this
        exact this
      have hk : val a ^ k ≤ val x := le_trans hpow_ge hk1
      have hr : val res = val a ^ k := heq hk
      have hvp : val (Nat.bits (val res * val a)) = val a ^ (k + 1) := by
        rw [val_bits, hr, Nat.pow_succ]
      have hflag : (if decide (val (Nat.bits (val res * val a)) ≤ val x) then [true] else []) = [true] := by
        rw [hvp]; simp only [hk1, decide_true, ↓reduceIte]
      rw [hflag, sel_cons, hvp]

theorem powCap_spec (x a u : List Bool) (hu : 1 ≤ u.length) :
    (val (powCap x a u) ≤ val x ↔ val a ^ u.length ≤ val x) ∧
      (val a ^ u.length ≤ val x → val (powCap x a u) = val a ^ u.length) := by
  by_cases ha0 : val a = 0
  · have hpow0 : val a ^ u.length = 0 := by
      rw [ha0]
      exact Nat.zero_pow (by omega)
    obtain ⟨m, hm⟩ : ∃ m, u.length = m + 1 := ⟨u.length - 1, by omega⟩
    obtain ⟨res, hres⟩ := powStep_iter_fst x a m
    have hrun : powStep^[u.length] (pairB (pairB x a) [true]) = pairB (pairB x a) (Nat.bits 0) := by
      rw [hm, Function.iterate_succ_apply', hres]
      simp only [powStep, pX, pA, pCur, unpairB_pairB, ha0, Nat.mul_zero, val_bits, Nat.zero_le,
        decide_true, ↓reduceIte, sel_cons]
    have hval : val (powCap x a u) = 0 := by
      unfold powCap
      rw [hrun, unpairB_pairB, val_bits]
    rw [hval, hpow0]
    exact ⟨Iff.rfl, fun _ => rfl⟩
  · have ha1 : 1 ≤ val a := by omega
    obtain ⟨res, hres, hiff, heq⟩ := powStep_iter_pos x a ha1 u.length
    unfold powCap
    rw [hres, unpairB_pairB]
    exact ⟨hiff, heq⟩

-- Part B: Integer k-th root binary search
-- State: pairB (pairB (pairB x u) bit) r
def rX (s : List Bool) : List Bool := (unpairB (unpairB (unpairB s).1).1).1
def rU (s : List Bool) : List Bool := (unpairB (unpairB (unpairB s).1).1).2
def rBit (s : List Bool) : List Bool := (unpairB (unpairB s).1).2
def rR (s : List Bool) : List Bool := (unpairB s).2

def rootCand (s : List Bool) : List Bool :=
  Nat.bits (val (rR s) + val (rBit s))

def rootStep (s : List Bool) : List Bool :=
  let x := rX s
  let u := rU s
  let bit := rBit s
  let r := rR s
  let cand := rootCand s
  let p := powCap x cand u
  let ok1 := if decide (val p ≤ val x) then [true] else []
  let ok2 := if decide (val cand ≤ val x) then [true] else []
  pairB (pairB (pairB x u) bit.tail) (sel ok1 r (sel ok2 r cand))

def rootMeasure (s : List Bool) : ℕ := (rX s).length + 10

theorem rootMeasure_step (s : List Bool) : rootMeasure (rootStep s) ≤ rootMeasure s := by
  simp only [rootMeasure, rootStep, rX, unpairB_pairB, le_refl]

theorem rootMeasure_linear (s : List Bool) : rootMeasure s ≤ 10 * s.length + 10 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  have h3 := unpairB_length (unpairB (unpairB s).1).1
  unfold rootMeasure rX
  omega

theorem rootStep_len (s : List Bool) : (rootStep s).length ≤ s.length + rootMeasure s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  have h3 := unpairB_length (unpairB (unpairB s).1).1
  have hbound : 8 * (rX s).length + 4 * (rU s).length + 2 * (rBit s).length + (rR s).length ≤ s.length := by
    unfold rX rU rBit rR
    omega
  unfold rootStep rootMeasure
  dsimp only
  rw [pairB_length, pairB_length, pairB_length, List.length_tail]
  by_cases h1c : val (powCap (rX s) (rootCand s) (rU s)) ≤ val (rX s)
  · have hf1 : (if decide (val (powCap (rX s) (rootCand s) (rU s)) ≤ val (rX s)) then [true] else []) = [true] := by
      simp only [h1c, decide_true, ↓reduceIte]
    rw [hf1, sel_cons]
    by_cases h2c : val (rootCand s) ≤ val (rX s)
    · have hf2 : (if decide (val (rootCand s) ≤ val (rX s)) then [true] else []) = [true] := by
        simp only [h2c, decide_true, ↓reduceIte]
      rw [hf2, sel_cons]
      have hlt : val (rR s) + val (rBit s) < 2 ^ (rX s).length := by
        have hx := val_lt_two_pow (rX s)
        unfold rootCand at h2c
        rw [val_bits] at h2c
        omega
      have hclen : (rootCand s).length ≤ (rX s).length :=
        length_bits_le (rX s).length (val (rR s) + val (rBit s)) hlt
      omega
    · have hf2 : (if decide (val (rootCand s) ≤ val (rX s)) then [true] else []) = [] := by
        simp only [h2c, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [hf2, sel_nil]
      omega
  · have hf1 : (if decide (val (powCap (rX s) (rootCand s) (rU s)) ≤ val (rX s)) then [true] else []) = [] := by
      simp only [h1c, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [hf1, sel_nil]
    omega

theorem cpt_rootStep : CPT rootStep := by
  have hX : CPT rX := cpt_unpairB1_1 (cpt_unpairB1_1 cpt_unpairB1)
  have hU : CPT rU := cpt_unpairB2_1 (cpt_unpairB1_1 cpt_unpairB1)
  have hBit : CPT rBit := cpt_unpairB2_1 cpt_unpairB1
  have hR : CPT rR := cpt_unpairB2
  have hCand : CPT rootCand := pp_cptE (cpt_comp (cpt_pair hR hBit) cpt_add) (fun _ => rfl)
  have hPowIn : CPT (fun s => pairB (pairB (rX s) (rootCand s)) (rU s)) :=
    cpt_pairB2 (cpt_pairB2 hX hCand) hU
  have hPow : CPT (fun s => powCap (rX s) (rootCand s) (rU s)) :=
    pp_cptE (cpt_comp hPowIn cpt_powCapS) (fun s => by
      simp only [pX, pA, pCur, unpairB_pairB])
  have hOk1 := cpt_bitFlag (cpt_comp (cpt_pair hPow hX) cpt_ble)
  have hOk2 := cpt_bitFlag (cpt_comp (cpt_pair hCand hX) cpt_ble)
  have hR' := cpt_sel hOk1 hR (cpt_sel hOk2 hR hCand)
  exact pp_cptE (cpt_pairB2 (cpt_pairB2 (cpt_pairB2 hX hU) (cpt_tail1 hBit)) hR') (fun _ => rfl)

theorem rootStep_iter (x u : List Bool) (hu : 2 ≤ u.length) :
    ∀ (m : ℕ) (r : List Bool),
      val r ^ u.length ≤ val x →
      val x < (val r + 2 ^ (m + 1)) ^ u.length →
      let res := (unpairB (rootStep^[m + 1] (pairB (pairB (pairB x u) (pow2List m)) r))).2
      val res ^ u.length ≤ val x ∧ val x < (val res + 1) ^ u.length := by
  intro m
  induction m with
  | zero =>
    intro r hlo hhi
    dsimp only
    rw [Nat.zero_add, Function.iterate_one]
    have hpow := powCap_spec x (Nat.bits (val r + 1)) u (by omega)
    have hbit0 : val (pow2List 0) = 1 := val_pow2List 0
    have hcand0 : val (Nat.bits (val r + 1)) = val r + 1 := val_bits (val r + 1)
    have hstep : rootStep (pairB (pairB (pairB x u) (pow2List 0)) r) =
        pairB (pairB (pairB x u) [])
          (sel (if decide (val (powCap x (Nat.bits (val r + 1)) u) ≤ val x) then [true] else []) r
            (sel (if decide (val (Nat.bits (val r + 1)) ≤ val x) then [true] else []) r
              (Nat.bits (val r + 1)))) := by
      simp only [rootStep, rootCand, rX, rU, rBit, rR, unpairB_pairB, hbit0]
      rfl
    rw [hstep, unpairB_pairB]
    by_cases h : (val r + 1) ^ u.length ≤ val x
    · have hp : val (powCap x (Nat.bits (val r + 1)) u) ≤ val x := by
        rw [hpow.1, hcand0]; exact h
      have hc : val (Nat.bits (val r + 1)) ≤ val x := by
        rw [hcand0]
        exact le_trans (Nat.le_self_pow (by omega) (val r + 1)) h
      have hf1 : (if decide (val (powCap x (Nat.bits (val r + 1)) u) ≤ val x) then [true] else []) = [true] := by
        simp only [hp, decide_true, ↓reduceIte]
      have hf2 : (if decide (val (Nat.bits (val r + 1)) ≤ val x) then [true] else []) = [true] := by
        simp only [hc, decide_true, ↓reduceIte]
      rw [hf1, sel_cons, hf2, sel_cons, hcand0]
      refine ⟨h, ?_⟩
      have heq : val r + 1 + 1 = val r + 2 ^ (0 + 1) := by omega
      rw [heq]; exact hhi
    · have hp : ¬ (val (powCap x (Nat.bits (val r + 1)) u) ≤ val x) := by
        rw [hpow.1, hcand0]; exact h
      have hf1 : (if decide (val (powCap x (Nat.bits (val r + 1)) u) ≤ val x) then [true] else []) = [] := by
        simp only [hp, decide_false, Bool.false_eq_true, ↓reduceIte]
      dsimp only
      rw [hf1, sel_nil]
      exact ⟨hlo, by omega⟩
  | succ m ih =>
    intro r hlo hhi
    dsimp only
    rw [Function.iterate_succ_apply]
    have htail : (pow2List (m + 1)).tail = pow2List m := rfl
    have hbitm : val (pow2List (m + 1)) = 2 ^ (m + 1) := val_pow2List (m + 1)
    have hcandm : val (Nat.bits (val r + 2 ^ (m + 1))) = val r + 2 ^ (m + 1) :=
      val_bits (val r + 2 ^ (m + 1))
    have hpow := powCap_spec x (Nat.bits (val r + 2 ^ (m + 1))) u (by omega)
    have hstep : rootStep (pairB (pairB (pairB x u) (pow2List (m + 1))) r) =
        pairB (pairB (pairB x u) (pow2List m))
          (sel (if decide (val (powCap x (Nat.bits (val r + 2 ^ (m + 1))) u) ≤ val x) then [true] else []) r
            (sel (if decide (val (Nat.bits (val r + 2 ^ (m + 1))) ≤ val x) then [true] else []) r
              (Nat.bits (val r + 2 ^ (m + 1))))) := by
      simp only [rootStep, rootCand, rX, rU, rBit, rR, unpairB_pairB, hbitm, htail]
    rw [hstep]
    by_cases h : (val r + 2 ^ (m + 1)) ^ u.length ≤ val x
    · have hp : val (powCap x (Nat.bits (val r + 2 ^ (m + 1))) u) ≤ val x := by
        rw [hpow.1, hcandm]; exact h
      have hc : val (Nat.bits (val r + 2 ^ (m + 1))) ≤ val x := by
        rw [hcandm]
        exact le_trans (Nat.le_self_pow (by omega) (val r + 2 ^ (m + 1))) h
      have hf1 : (if decide (val (powCap x (Nat.bits (val r + 2 ^ (m + 1))) u) ≤ val x) then [true] else []) = [true] := by
        simp only [hp, decide_true, ↓reduceIte]
      have hf2 : (if decide (val (Nat.bits (val r + 2 ^ (m + 1))) ≤ val x) then [true] else []) = [true] := by
        simp only [hc, decide_true, ↓reduceIte]
      rw [hf1, sel_cons, hf2, sel_cons]
      refine ih (Nat.bits (val r + 2 ^ (m + 1))) (by rw [hcandm]; exact h) ?_
      rw [hcandm]
      have heq : val r + 2 ^ (m + 1) + 2 ^ (m + 1) = val r + 2 ^ (m + 1 + 1) := by
        rw [Nat.pow_succ]; omega
      rw [heq]
      exact hhi
    · have hp : ¬ (val (powCap x (Nat.bits (val r + 2 ^ (m + 1))) u) ≤ val x) := by
        rw [hpow.1, hcandm]; exact h
      have hf1 : (if decide (val (powCap x (Nat.bits (val r + 2 ^ (m + 1))) u) ≤ val x) then [true] else []) = [] := by
        simp only [hp, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [hf1, sel_nil]
      exact ih r hlo (by omega)

def rootFinal (x u : List Bool) : List Bool :=
  (unpairB (rootStep^[(pow2List x.length).length]
    (pairB (pairB (pairB x u) (pow2List x.length)) []))).2

theorem cpt_rootFinalS : CPT (fun s => rootFinal (unpairB s).1 (unpairB s).2) := by
  have hX : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hU : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hP2 := cpt_comp hX cpt_pow2
  have hInit := cpt_pairB2 (cpt_pairB2 (cpt_pairB2 hX hU) hP2) (cpt_const [])
  obtain ⟨cRoot⟩ := cpt_rootStep
  have hIter := Iter.iter_polyTime_measure rootStep cRoot rootMeasure 10
    rootMeasure_step rootStep_len rootMeasure_linear
  exact pp_cptE (cpt_unpairB2_1 (cpt_comp (cpt_pair hInit hP2) hIter)) (fun _ => rfl)

theorem rootFinal_spec (x u : List Bool) (hu : 2 ≤ u.length) :
    val (rootFinal x u) ^ u.length ≤ val x ∧ val x < (val (rootFinal x u) + 1) ^ u.length := by
  have hlo0 : val [] ^ u.length ≤ val x := by
    rw [val_nil, Nat.zero_pow (by omega)]
    exact Nat.zero_le _
  have hhi0 : val x < (val [] + 2 ^ (x.length + 1)) ^ u.length := by
    rw [val_nil, Nat.zero_add]
    have hx := val_lt_two_pow x
    have h1 : 2 ^ x.length ≤ 2 ^ (x.length + 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ (x.length + 1) ≤ (2 ^ (x.length + 1)) ^ u.length :=
      Nat.le_self_pow (by omega) _
    omega
  have hres := rootStep_iter x u hu x.length [] hlo0 hhi0
  simpa only [rootFinal, pow2List_length] using hres

-- Part C: Combined verifier checkV (x, u) and bounded unary search
private theorem ne_true (l : List Bool) :
    fstRun (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool))) (fun q => some q) true l =
      [true] := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp only [fstRun, Option.toList_none, List.nil_append, ih]

private theorem cpt_nonEmpty :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun l : List Bool => !l.isEmpty) :=
  fst_polyTime _ _ _ (fun (_ : Bool) (_ : Bool) => (true, (none : Option Bool)))
    (fun q => some q) false (fun l => by
      cases l with
      | nil => rfl
      | cons _ l =>
        simp only [List.isEmpty_cons, Bool.not_false, Computability.encodeBool, fstRun,
          Option.toList_none, List.nil_append, ne_true]
        rfl)

def checkFlag (s : List Bool) : List Bool :=
  let x := (unpairB s).1
  let u := (unpairB s).2
  sel u.tail
    (if decide (val x ≤ val [true]) then [true] else [])
    (if decide (val x ≤ val (powCap x (rootFinal x u) u)) then [true] else [])

theorem cpt_checkFlag : CPT checkFlag := by
  have hX : CPT (fun s => (unpairB s).1) := cpt_unpairB1
  have hU : CPT (fun s => (unpairB s).2) := cpt_unpairB2
  have hSmall := cpt_bitFlag (cpt_comp (cpt_pair hX (cpt_const [true])) cpt_ble)
  have hRF := cpt_rootFinalS
  have hPow : CPT (fun s => powCap (unpairB s).1 (rootFinal (unpairB s).1 (unpairB s).2) (unpairB s).2) :=
    pp_cptE (cpt_comp (cpt_pairB2 (cpt_pairB2 hX hRF) hU) cpt_powCapS) (fun s => by
      simp only [pX, pA, pCur, unpairB_pairB])
  have hGe2 := cpt_bitFlag (cpt_comp (cpt_pair hX hPow) cpt_ble)
  exact pp_cptE (cpt_sel (cpt_tail1 hU) hSmall hGe2) (fun _ => rfl)

def checkV (p : List Bool × List Bool) : Bool :=
  !(checkFlag (pairB p.1 p.2)).isEmpty

theorem cpt_checkV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer checkV := by
  rw [encodePair_eq]
  exact pp_cptE (cpt_comp cpt_pairB (cpt_comp cpt_checkFlag cpt_nonEmpty)) (fun _ => rfl)

theorem checkV_lt_two (x : List Bool) (i : ℕ) (hi : i < 2) :
    checkV (x, List.replicate i true) = true ↔ val x ≤ 1 := by
  have htail : (List.replicate i true).tail = [] := by
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl <;> rfl
  have h1 : val [true] = 1 := by
    simp only [val_cons, val_nil, Bool.toNat_true, Nat.mul_zero, Nat.add_zero]
  simp only [checkV, checkFlag, unpairB_pairB, htail, sel_nil, h1]
  by_cases hx : val x ≤ 1
  · simp only [hx, decide_true, ↓reduceIte, List.isEmpty_cons, Bool.not_false]
  · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil, Bool.not_true]

theorem checkV_ge_two (x : List Bool) (i : ℕ) (hi : 2 ≤ i) :
    checkV (x, List.replicate i true) = true ↔ ∃ a : ℕ, a ^ i = val x := by
  set u := List.replicate i true
  have hulen : u.length = i := List.length_replicate
  have htail_ne : u.tail ≠ [] := by
    have hlen : u.tail.length = i - 1 := by rw [List.length_tail, hulen]
    intro h0
    rw [h0, List.length_nil] at hlen
    omega
  have hsel : sel u.tail
      (if decide (val x ≤ val [true]) then [true] else [])
      (if decide (val x ≤ val (powCap x (rootFinal x u) u)) then [true] else []) =
      if decide (val x ≤ val (powCap x (rootFinal x u) u)) then [true] else [] := by
    unfold sel
    simp only [htail_ne, ↓reduceIte]
  have hrf := rootFinal_spec x u (by omega)
  have hpc := powCap_spec x (rootFinal x u) u (by omega)
  have hval_pc : val (powCap x (rootFinal x u) u) = val (rootFinal x u) ^ i := by
    rw [← hulen]
    exact hpc.2 hrf.1
  have hchk : checkV (x, u) = true ↔ val x ≤ val (rootFinal x u) ^ i := by
    simp only [checkV, checkFlag, unpairB_pairB]
    rw [hsel, hval_pc]
    by_cases h : val x ≤ val (rootFinal x u) ^ i
    · simp only [h, decide_true, ↓reduceIte, List.isEmpty_cons, Bool.not_false]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil, Bool.not_true]
  rw [hchk]
  rw [hulen] at hrf
  constructor
  · intro hge
    exact ⟨val (rootFinal x u), by omega⟩
  · rintro ⟨a, ha⟩
    have ha_eq : a = val (rootFinal x u) := by
      by_cases hlt : a < val (rootFinal x u)
      · exfalso
        have hp := Nat.pow_lt_pow_left hlt (by omega : i ≠ 0)
        omega
      · by_cases hgt : val (rootFinal x u) < a
        · exfalso
          have hle : val (rootFinal x u) + 1 ≤ a := by omega
          have hp := Nat.pow_le_pow_left hle i
          omega
        · omega
    rw [← ha_eq, ha]

theorem main_proof :
    ({x : List Bool | ∃ a k : ℕ, 2 ≤ k ∧ a ^ k = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} :
      Language Bool) ∈ PvsNP.P := by
  have hdec := PvsNP.Units.m2_bounded_unary_search_polytime checkV cpt_checkV
  refine ⟨fun x => (List.range (x.length + 1)).any (fun i => checkV (x, List.replicate i true)),
    hdec, fun x => ?_⟩
  change (∃ a k : ℕ, 2 ≤ k ∧ a ^ k = val x) ↔
    (List.range (x.length + 1)).any (fun i => checkV (x, List.replicate i true)) = true
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, k, hk2, hak⟩
    by_cases hx1 : val x ≤ 1
    · refine ⟨0, List.mem_range.mpr (by omega), ?_⟩
      exact (checkV_lt_two x 0 (by decide)).mpr hx1
    · have ha2 : 2 ≤ a := by
        by_cases ha0 : a = 0
        · rw [ha0, Nat.zero_pow (by omega)] at hak; omega
        · by_cases ha1 : a = 1
          · rw [ha1, Nat.one_pow] at hak; omega
          · omega
      have h2k : 2 ^ k < 2 ^ x.length := by
        have h1 : 2 ^ k ≤ a ^ k := Nat.pow_le_pow_left ha2 k
        have h2 := val_lt_two_pow x
        omega
      have hklt : k < x.length := by
        by_cases hge : x.length ≤ k
        · exfalso
          have := Nat.pow_le_pow_right (by decide : 0 < 2) hge
          omega
        · omega
      refine ⟨k, List.mem_range.mpr (by omega), ?_⟩
      exact (checkV_ge_two x k hk2).mpr ⟨a, hak⟩
  · rintro ⟨i, _, hvi⟩
    by_cases hi2 : i < 2
    · have hx1 := (checkV_lt_two x i hi2).mp hvi
      by_cases hx0 : val x = 0
      · exact ⟨0, 2, le_refl 2, by rw [Nat.zero_pow (by decide)]; exact hx0.symm⟩
      · have hx1' : val x = 1 := by omega
        exact ⟨1, 2, le_refl 2, by rw [Nat.one_pow]; exact hx1'.symm⟩
    · have hi2' : 2 ≤ i := by omega
      obtain ⟨a, ha⟩ := (checkV_ge_two x i hi2').mp hvi
      exact ⟨a, i, hi2', ha⟩

end PvsNP.Units.tl_lang_val_perfect_power_p

theorem PvsNP.Units.tl_lang_val_perfect_power_p :
    ({x : List Bool | ∃ a k : ℕ, 2 ≤ k ∧ a ^ k = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} :
      Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_val_perfect_power_p.main_proof
