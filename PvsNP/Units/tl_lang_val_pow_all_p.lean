import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.tf_fun_pair_add
import PvsNP.Units.tf_fun_pair_mul

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_val_pow_all_p

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

lemma encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := by
  funext ⟨a, b⟩
  rfl

lemma encodeString_eq :
    PvsNP.encodeString = (fun x : List Bool => x) := by
  funext x
  rfl

def val (l : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (l.map Bool.toNat)

lemma val_nil : val [] = 0 := rfl

lemma val_cons (b : Bool) (l : List Bool) :
    val (b :: l) = b.toNat + 2 * val l := by
  simp [val, Nat.ofDigits_cons]

lemma val_lt_two_pow (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp [val_nil]
  | cons b rest ih =>
    rw [val_cons, List.length_cons, pow_succ']
    cases b <;> simp <;> omega

lemma val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero => simp [val]
  | bit b n ih =>
    by_cases h : b = false ∧ n = 0
    · rcases h with ⟨rfl, rfl⟩
      simp [val]
    · rw [Nat.bits_append_bit n b (fun hn => by cases b <;> simp_all), val_cons, ih, Nat.bit_val]
      cases b
      · simp
      · simp; ring

lemma length_bits_le (k : ℕ) : ∀ n : ℕ, n < 2 ^ k → (Nat.bits n).length ≤ k := by
  induction k with
  | zero =>
    intro n hn
    have h0 : n = 0 := by omega
    subst h0
    simp
  | succ k ih =>
    intro n hn
    induction n using Nat.binaryRec with
    | zero => simp
    | bit b m _ =>
      by_cases h : b = false ∧ m = 0
      · rcases h with ⟨rfl, rfl⟩
        simp
      · rw [Nat.bits_append_bit m b (fun hm => by cases b <;> simp_all), List.length_cons]
        have hm : m < 2 ^ k := by
          rw [Nat.bit_val, pow_succ'] at hn
          cases b <;> simp at hn <;> omega
        have := ih m hm
        omega

def pow2List (k : ℕ) : List Bool :=
  List.replicate k false ++ [true]

lemma val_pow2List (k : ℕ) : val (pow2List k) = 2 ^ k := by
  induction k with
  | zero => simp [pow2List, val_cons, val_nil]
  | succ k ih =>
    simp only [pow2List, List.replicate_succ, List.cons_append, val_cons, Bool.toNat_false,
      Nat.zero_add] at ih ⊢
    rw [ih, pow_succ']

lemma pow2List_length (k : ℕ) : (pow2List k).length = k + 1 := by
  simp [pow2List]

lemma cpt_zeros :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => List.replicate x.length false) := by
  rw [encodeString_eq]
  refine filterMap_polyTime _ _ _ (fun _ : Bool => some false) ?_
  intro x
  induction x with
  | nil => rfl
  | cons _ rest ih =>
    simp only [List.length_cons, List.replicate_succ, List.filterMap_cons] at ih ⊢
    exact congrArg (List.cons false) ih

lemma toCpt {f : List Bool → List Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f := hf

lemma fromCptPair {f : List Bool → List Bool × List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair f) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair f := by
  rw [← encodePair_eq, encodeString_eq]
  exact hf

def sX (s : List Bool) : List Bool := (unpairB (unpairB s).1).1
def sBit (s : List Bool) : List Bool := (unpairB (unpairB s).1).2
def sR (s : List Bool) : List Bool := (unpairB s).2

def candR (s : List Bool) : List Bool :=
  Nat.bits (val (sR s) + val (sBit s))

def powBits : ℕ → List Bool → List Bool
  | 0, _ => [true]
  | m + 1, c => Nat.bits (val (powBits m c) * val c)

lemma val_powBits (m : ℕ) (c : List Bool) : val (powBits m c) = (val c) ^ m := by
  induction m with
  | zero => simp [powBits, val_cons, val_nil]
  | succ m ih =>
    simp only [powBits, val_bits, ih, pow_succ]

lemma powBits_poly : ∀ m : ℕ,
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (powBits m)
  | 0 => by
    rw [encodeString_eq]
    exact cpt_const [true]
  | m + 1 => by
    have ih := powBits_poly m
    have hpair := fromCptPair (cpt_pair (toCpt ih) cpt_id)
    have hmul := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun c => (powBits m c, c))
      (fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2))
      hpair PvsNP.Units.tf_fun_pair_mul
    have heq : ((fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2)) ∘
        (fun c => (powBits m c, c))) = powBits (m + 1) := by
      funext c; rfl
    rwa [heq] at hmul

def powCand (e : ℕ) (s : List Bool) : List Bool :=
  powBits e (candR s)

def powStep (e : ℕ) (s : List Bool) : List Bool :=
  pairB (pairB (sX s) (sBit s).tail)
    (if decide (val (powCand e s) ≤ val (sX s)) = true then candR s else sR s)

def powMeasure (s : List Bool) : ℕ :=
  (sX s).length + 4

lemma powMeasure_step (e : ℕ) (s : List Bool) :
    powMeasure (powStep e s) ≤ powMeasure s := by
  simp [powMeasure, powStep, sX, unpairB_pairB]

lemma powMeasure_linear (s : List Bool) :
    powMeasure s ≤ 4 * s.length + 4 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  unfold powMeasure sX
  omega

lemma powStep_len (e : ℕ) (he : 1 ≤ e) (s : List Bool) :
    (powStep e s).length ≤ s.length + powMeasure s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  have hbt : (sBit s).tail.length ≤ (sBit s).length := by simp
  have hbound : 4 * (sX s).length + 2 * (sBit s).length + (sR s).length ≤ s.length := by
    unfold sX sBit sR; omega
  unfold powStep powMeasure
  simp only [pairB_length]
  by_cases hok : decide (val (powCand e s) ≤ val (sX s)) = true
  · simp only [hok, ↓reduceIte]
    simp only [decide_eq_true_eq] at hok
    have hval_pow : val (powCand e s) = (val (candR s)) ^ e := val_powBits e (candR s)
    have hle_x : val (candR s) < 2 ^ (sX s).length := by
      have hxlt := val_lt_two_pow (sX s)
      have hpow : val (candR s) ≤ (val (candR s)) ^ e := Nat.le_self_pow (by omega : e ≠ 0) _
      omega
    have hclen : (candR s).length ≤ (sX s).length := by
      have hbits := length_bits_le (sX s).length (val (sR s) + val (sBit s))
      have hval_c : val (candR s) = val (sR s) + val (sBit s) := val_bits _
      exact hbits (by omega)
    omega
  · simp only [hok, Bool.false_eq_true, ↓reduceIte]
    omega

lemma powStep_poly (e : ℕ) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (powStep e) := by
  have hadd : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits (val p.1 + val p.2)) :=
    PvsNP.Units.tf_fun_pair_add
  have hle : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2)) :=
    PvsNP.Units.m2_binary_le_polytime
  have hX : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) sX :=
    cpt_unpairB1_1 cpt_unpairB1
  have hBit : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) sBit :=
    cpt_unpairB2_1 cpt_unpairB1
  have hR : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) sR :=
    cpt_unpairB2
  have hpairRB := fromCptPair (cpt_pair hR hBit)
  have hcand0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun s => (sR s, sBit s))
      (fun p : List Bool × List Bool => Nat.bits (val p.1 + val p.2))
      hpairRB hadd
  have hcand : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString candR := by
    have heq : ((fun p : List Bool × List Bool => Nat.bits (val p.1 + val p.2)) ∘
        (fun s => (sR s, sBit s))) = candR := by
      funext s; rfl
    rwa [heq] at hcand0
  have hpow0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      candR (powBits e) hcand (powBits_poly e)
  have hpow : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (powCand e) := by
    have heq : (powBits e ∘ candR) = powCand e := by funext s; rfl
    rwa [heq] at hpow0
  have hpairPX := fromCptPair (cpt_pair (toCpt hpow) hX)
  have hok0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
      (fun s => (powCand e s, sX s))
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2))
      hpairPX hle
  have hok : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide (val (powCand e s) ≤ val (sX s))) := by
    have heq : ((fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2)) ∘
        (fun s => (powCand e s, sX s))) = (fun s => decide (val (powCand e s) ≤ val (sX s))) := by
      funext s; rfl
    rwa [heq] at hok0
  have hrNext : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => if decide (val (powCand e s) ≤ val (sX s)) = true then candR s else sR s) :=
    PvsNP.Units.m2_ite_polytime
      (fun s => decide (val (powCand e s) ≤ val (sX s))) candR sR hok hcand hR
  have hstep0 := cpt_pairB2 (cpt_pairB2 hX (cpt_tail1 hBit)) (toCpt hrNext)
  have heq : (fun s => pairB (pairB (sX s) (sBit s).tail)
      (if decide (val (powCand e s) ≤ val (sX s)) = true then candR s else sR s)) = powStep e := by
    funext s; rfl
  rw [encodeString_eq, ← heq]
  exact hstep0

lemma powStep_iter (e : ℕ) (x : List Bool) :
    ∀ (k : ℕ) (r : List Bool),
      (val r) ^ e ≤ val x →
      val x < (val r + 2 ^ (k + 1)) ^ e →
      let res := (unpairB ((powStep e)^[k + 1] (pairB (pairB x (pow2List k)) r))).2
      (val res) ^ e ≤ val x ∧ val x < (val res + 1) ^ e := by
  intro k
  induction k with
  | zero =>
    intro r hlo hhi
    simp only [Nat.zero_add, Function.iterate_one]
    have hs : powStep e (pairB (pairB x (pow2List 0)) r) =
        pairB (pairB x [])
          (if decide ((val r + 1) ^ e ≤ val x) = true then
            Nat.bits (val r + 1) else r) := by
      unfold powStep powCand candR sX sBit sR
      simp only [unpairB_pairB, val_pow2List, pow_zero, val_powBits, val_bits]
      rfl
    rw [hs, unpairB_pairB]
    by_cases h : (val r + 1) ^ e ≤ val x
    · simp only [decide_eq_true h, ↓reduceIte, val_bits]
      refine ⟨h, ?_⟩
      have h2 : val r + 1 + 1 = val r + 2 ^ 1 := by omega
      rw [h2]
      exact hhi
    · simp only [decide_eq_false h, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hlo, Nat.lt_of_not_ge h⟩
  | succ k ih =>
    intro r hlo hhi
    rw [Function.iterate_succ_apply]
    have htail : (pow2List (k + 1)).tail = pow2List k := rfl
    have hs : powStep e (pairB (pairB x (pow2List (k + 1))) r) =
        pairB (pairB x (pow2List k))
          (if decide ((val r + 2 ^ (k + 1)) ^ e ≤ val x) = true then
            Nat.bits (val r + 2 ^ (k + 1)) else r) := by
      unfold powStep powCand candR sX sBit sR
      simp only [unpairB_pairB, val_pow2List, val_powBits, val_bits, htail]
    rw [hs]
    by_cases h : (val r + 2 ^ (k + 1)) ^ e ≤ val x
    · simp only [h, decide_true, ↓reduceIte]
      apply ih (Nat.bits (val r + 2 ^ (k + 1)))
      · rw [val_bits]; exact h
      · rw [val_bits]
        have heq : val r + 2 ^ (k + 1) + 2 ^ (k + 1) = val r + 2 ^ (k + 1 + 1) := by
          rw [pow_succ]; ring
        rw [heq]
        exact hhi
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih r hlo (Nat.lt_of_not_ge h)

def rFinal (e : ℕ) (x : List Bool) : List Bool :=
  (unpairB ((powStep e)^[(pow2List x.length).length]
    (pairB (pairB x (pow2List x.length)) []))).2

def powDecider (e : ℕ) (x : List Bool) : Bool :=
  decide (val x ≤ val (powBits e (rFinal e x)))

theorem main_proof_ge1 (e : ℕ) (he : 1 ≤ e) :
    ({x : List Bool | ∃ k : ℕ, Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = k ^ e} :
      Language Bool) ∈ PvsNP.P := by
  obtain ⟨cs⟩ := powStep_poly e
  have hiter : PvsNP.PolyTimeComputable
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => (powStep e)^[p.2.length] p.1) :=
    Iter.iter_polyTime_measure (powStep e) cs powMeasure 4
      (powMeasure_step e) (powStep_len e he) powMeasure_linear
  have hpow2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => pow2List x.length) :=
    cpt_app2 cpt_zeros (cpt_const [true])
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => pairB (pairB x (pow2List x.length)) []) :=
    cpt_pairB2 (cpt_pairB2 cpt_id hpow2) (cpt_const [])
  have hrFinal : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (rFinal e) :=
    cpt_unpairB2_1
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString
        PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
        _ _ (cpt_pair hinit hpow2) hiter)
  have hpowFinal : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => powBits e (rFinal e x)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeString
      (rFinal e) (powBits e) hrFinal (powBits_poly e)
  have hpairXS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x => (x, powBits e (rFinal e x))) := by
    rw [← encodePair_eq, encodeString_eq]
    exact cpt_pair cpt_id hpowFinal
  have hdec : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (powDecider e) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
      (fun x => (x, powBits e (rFinal e x)))
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2))
      hpairXS PvsNP.Units.m2_binary_le_polytime
  refine ⟨powDecider e, hdec, ?_⟩
  intro x
  change (∃ k : ℕ, val x = k ^ e) ↔ powDecider e x = true
  have hhi0 : val x < (val [] + 2 ^ (x.length + 1)) ^ e := by
    have hlt := val_lt_two_pow x
    have h1 : 2 ^ x.length ≤ 2 ^ (x.length + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ (x.length + 1) ≤ (2 ^ (x.length + 1)) ^ e :=
      Nat.le_self_pow (by omega : e ≠ 0) _
    simp only [val_nil, Nat.zero_add]
    omega
  have hres := powStep_iter e x x.length [] (by simp [val_nil, Nat.zero_pow he]) hhi0
  have hrf_lo : (val (rFinal e x)) ^ e ≤ val x := by
    simpa [rFinal, pow2List_length] using hres.1
  have hrf_hi : val x < (val (rFinal e x) + 1) ^ e := by
    simpa [rFinal, pow2List_length] using hres.2
  simp only [powDecider, decide_eq_true_eq, val_powBits]
  constructor
  · rintro ⟨k, hk⟩
    have hkeq : k = val (rFinal e x) := by
      have h1 : (val (rFinal e x)) ^ e ≤ k ^ e := by omega
      have h2 : k ^ e < (val (rFinal e x) + 1) ^ e := by omega
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have hltp : k ^ e < (val (rFinal e x)) ^ e := Nat.pow_lt_pow_left hlt (by omega : e ≠ 0)
        omega
      · have hgep : (val (rFinal e x) + 1) ^ e ≤ k ^ e :=
          Nat.pow_le_pow_left (Nat.succ_le_of_lt hgt) e
        omega
    rw [hk, hkeq]
  · intro hge
    refine ⟨val (rFinal e x), ?_⟩
    omega

theorem main_proof_zero :
    ({x : List Bool | ∃ k : ℕ, Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = k ^ 0} :
      Language Bool) ∈ PvsNP.P := by
  let decLe1 : List Bool → Bool := fun x => decide (val x ≤ val [true])
  let decGe1 : List Bool → Bool := fun x => decide (val [true] ≤ val x)
  let flagGe1 : List Bool → List Bool := fun x => if decGe1 x = true then [true] else []
  let flagEq1 : List Bool → List Bool := fun x => if decLe1 x = true then flagGe1 x else []
  let dec0 : List Bool → Bool := fun x => decide (val [true] ≤ val (flagEq1 x))
  have hpairLe1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (x, [true])) := by
    rw [← encodePair_eq, encodeString_eq]
    exact cpt_pair cpt_id (cpt_const [true])
  have hdecLe1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer decLe1 :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
      (fun x => (x, [true]))
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2))
      hpairLe1 PvsNP.Units.m2_binary_le_polytime
  have hpairGe1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => ([true], x)) := by
    rw [← encodePair_eq, encodeString_eq]
    exact cpt_pair (cpt_const [true]) cpt_id
  have hdecGe1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer decGe1 :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
      (fun x => ([true], x))
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2))
      hpairGe1 PvsNP.Units.m2_binary_le_polytime
  have hconst1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun _ : List Bool => ([true] : List Bool)) := by
    rw [encodeString_eq]; exact cpt_const [true]
  have hconst0 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun _ : List Bool => ([] : List Bool)) := by
    rw [encodeString_eq]; exact cpt_const []
  have hflagGe1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString flagGe1 :=
    PvsNP.Units.m2_ite_polytime decGe1 (fun _ => [true]) (fun _ => []) hdecGe1 hconst1 hconst0
  have hflagEq1 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString flagEq1 :=
    PvsNP.Units.m2_ite_polytime decLe1 flagGe1 (fun _ => []) hdecLe1 hflagGe1 hconst0
  have hpairOut : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => ([true], flagEq1 x)) := by
    rw [← encodePair_eq, encodeString_eq]
    exact cpt_pair (cpt_const [true]) (toCpt hflagEq1)
  have hdec0 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer dec0 :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
      (fun x => ([true], flagEq1 x))
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2))
      hpairOut PvsNP.Units.m2_binary_le_polytime
  refine ⟨dec0, hdec0, ?_⟩
  intro x
  change (∃ k : ℕ, val x = k ^ 0) ↔ dec0 x = true
  have hv1 : val [true] = 1 := by simp [val_cons, val_nil]
  have hv0 : val [] = 0 := val_nil
  constructor
  · rintro ⟨k, hk⟩
    simp only [pow_zero] at hk
    simp [dec0, flagEq1, flagGe1, decLe1, decGe1, hv1, hk]
  · intro hd
    refine ⟨1, ?_⟩
    simp only [pow_zero]
    by_cases hle : val x ≤ 1
    · by_cases hge : 1 ≤ val x
      · omega
      · simp [dec0, flagEq1, flagGe1, decLe1, decGe1, hv1, hv0, hle, hge] at hd
    · simp [dec0, flagEq1, flagGe1, decLe1, decGe1, hv1, hv0, hle] at hd

end PvsNP.Units.tl_lang_val_pow_all_p

theorem PvsNP.Units.tl_lang_val_pow_all_p :
    ∀ e : ℕ, ({x : List Bool | ∃ k : ℕ, Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = k ^ e} : Language Bool) ∈ PvsNP.P := by
  intro e
  cases e with
  | zero => exact PvsNP.Units.tl_lang_val_pow_all_p.main_proof_zero
  | succ e' => exact PvsNP.Units.tl_lang_val_pow_all_p.main_proof_ge1 (e' + 1) (Nat.succ_pos e')
