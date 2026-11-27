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

namespace PvsNP.Units.tl_lang_val_pow_p

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

def sX (s : List Bool) : List Bool := (unpairB (unpairB s).1).1
def sBit (s : List Bool) : List Bool := (unpairB (unpairB s).1).2
def sR (s : List Bool) : List Bool := (unpairB s).2

def candR (s : List Bool) : List Bool :=
  Nat.bits (val (sR s) + val (sBit s))

def sqCand (s : List Bool) : List Bool :=
  Nat.bits (val (candR s) * val (candR s))

def sqrtStep (s : List Bool) : List Bool :=
  pairB (pairB (sX s) (sBit s).tail)
    (if decide (val (sqCand s) ≤ val (sX s)) = true then candR s else sR s)

def sqrtMeasure (s : List Bool) : ℕ :=
  (sX s).length + 4

lemma sqrtMeasure_step (s : List Bool) :
    sqrtMeasure (sqrtStep s) ≤ sqrtMeasure s := by
  simp [sqrtMeasure, sqrtStep, sX, unpairB_pairB]

lemma sqrtMeasure_linear (s : List Bool) :
    sqrtMeasure s ≤ 4 * s.length + 4 := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  unfold sqrtMeasure sX
  omega

lemma sqrtStep_len (s : List Bool) :
    (sqrtStep s).length ≤ s.length + sqrtMeasure s := by
  have h1 := unpairB_length s
  have h2 := unpairB_length (unpairB s).1
  have hbt : (sBit s).tail.length ≤ (sBit s).length := by simp
  have hbound : 4 * (sX s).length + 2 * (sBit s).length + (sR s).length ≤ s.length := by
    unfold sX sBit sR; omega
  unfold sqrtStep sqrtMeasure
  simp only [pairB_length]
  by_cases hok : decide (val (sqCand s) ≤ val (sX s)) = true
  · simp only [hok, ↓reduceIte]
    simp only [decide_eq_true_eq] at hok
    have hval_sq : val (sqCand s) = val (candR s) * val (candR s) := val_bits _
    have hle_x : val (candR s) < 2 ^ (sX s).length := by
      have hxlt := val_lt_two_pow (sX s)
      have hsq : val (candR s) ≤ val (candR s) * val (candR s) := Nat.le_mul_self _
      omega
    have hclen : (candR s).length ≤ (sX s).length := by
      have hbits := length_bits_le (sX s).length (val (sR s) + val (sBit s))
      have hval_c : val (candR s) = val (sR s) + val (sBit s) := val_bits _
      exact hbits (by omega)
    omega
  · simp only [hok, Bool.false_eq_true, ↓reduceIte]
    omega

lemma toCpt {f : List Bool → List Bool}
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f := hf

lemma fromCptPair {f : List Bool → List Bool × List Bool}
    (hf : ComputableInPolyTime (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair f) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair f := by
  rw [← encodePair_eq, encodeString_eq]
  exact hf

lemma sqrtStep_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sqrtStep := by
  have hadd : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits (val p.1 + val p.2)) :=
    PvsNP.Units.tf_fun_pair_add
  have hmul : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2)) :=
    PvsNP.Units.tf_fun_pair_mul
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
      funext s; dsimp only [Function.comp_apply]; unfold candR; rfl
    rwa [heq] at hcand0
  have hpairCC := fromCptPair (cpt_pair (toCpt hcand) (toCpt hcand))
  have hsq0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun s => (candR s, candR s))
      (fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2))
      hpairCC hmul
  have hsq : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sqCand := by
    have heq : ((fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2)) ∘
        (fun s => (candR s, candR s))) = sqCand := by
      funext s; dsimp only [Function.comp_apply]; unfold sqCand; rfl
    rwa [heq] at hsq0
  have hpairSX := fromCptPair (cpt_pair (toCpt hsq) hX)
  have hok0 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
      (fun s => (sqCand s, sX s))
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2))
      hpairSX hle
  have hok : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide (val (sqCand s) ≤ val (sX s))) := by
    have heq : ((fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2)) ∘
        (fun s => (sqCand s, sX s))) = (fun s => decide (val (sqCand s) ≤ val (sX s))) := by
      funext s; dsimp only [Function.comp_apply]
    rwa [heq] at hok0
  have hrNext : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => if decide (val (sqCand s) ≤ val (sX s)) = true then candR s else sR s) :=
    PvsNP.Units.m2_ite_polytime
      (fun s => decide (val (sqCand s) ≤ val (sX s))) candR sR hok hcand hR
  have hstep0 := cpt_pairB2 (cpt_pairB2 hX (cpt_tail1 hBit)) (toCpt hrNext)
  have heq : (fun s => pairB (pairB (sX s) (sBit s).tail)
      (if decide (val (sqCand s) ≤ val (sX s)) = true then candR s else sR s)) = sqrtStep := by
    funext s; unfold sqrtStep; rfl
  rw [encodeString_eq, ← heq]
  exact hstep0

lemma sqrtStep_iter (x : List Bool) :
    ∀ (k : ℕ) (r : List Bool),
      val r * val r ≤ val x →
      val x < (val r + 2 ^ (k + 1)) * (val r + 2 ^ (k + 1)) →
      let res := (unpairB (sqrtStep^[k + 1] (pairB (pairB x (pow2List k)) r))).2
      val res * val res ≤ val x ∧ val x < (val res + 1) * (val res + 1) := by
  intro k
  induction k with
  | zero =>
    intro r hlo hhi
    simp only [Nat.zero_add, Function.iterate_one]
    have hs : sqrtStep (pairB (pairB x (pow2List 0)) r) =
        pairB (pairB x [])
          (if decide ((val r + 1) * (val r + 1) ≤ val x) = true then
            Nat.bits (val r + 1) else r) := by
      unfold sqrtStep sqCand candR sX sBit sR
      simp only [unpairB_pairB, val_pow2List, pow_zero, val_bits]
      rfl
    rw [hs, unpairB_pairB]
    by_cases h : (val r + 1) * (val r + 1) ≤ val x
    · simp only [decide_eq_true h, ↓reduceIte, val_bits]
      exact ⟨h, by simpa using hhi⟩
    · simp only [decide_eq_false h, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hlo, by omega⟩
  | succ k ih =>
    intro r hlo hhi
    rw [Function.iterate_succ_apply]
    have htail : (pow2List (k + 1)).tail = pow2List k := rfl
    have hs : sqrtStep (pairB (pairB x (pow2List (k + 1))) r) =
        pairB (pairB x (pow2List k))
          (if decide ((val r + 2 ^ (k + 1)) * (val r + 2 ^ (k + 1)) ≤ val x) = true then
            Nat.bits (val r + 2 ^ (k + 1)) else r) := by
      unfold sqrtStep sqCand candR sX sBit sR
      simp only [unpairB_pairB, val_pow2List, val_bits, htail]
    rw [hs]
    by_cases h : (val r + 2 ^ (k + 1)) * (val r + 2 ^ (k + 1)) ≤ val x
    · simp only [h, decide_true, ↓reduceIte]
      apply ih (Nat.bits (val r + 2 ^ (k + 1)))
      · rw [val_bits]; exact h
      · rw [val_bits]
        have heq : val r + 2 ^ (k + 1) + 2 ^ (k + 1) = val r + 2 ^ (k + 1 + 1) := by
          rw [pow_succ]; ring
        rw [heq]
        exact hhi
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih r hlo (by omega)

def rFinal (x : List Bool) : List Bool :=
  (unpairB (sqrtStep^[(pow2List x.length).length]
    (pairB (pairB x (pow2List x.length)) []))).2

def sqDecider (x : List Bool) : Bool :=
  decide (val x ≤ val (Nat.bits (val (rFinal x) * val (rFinal x))))

theorem main_proof :
    ({x : List Bool | ∃ k : ℕ, Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = k ^ 2} :
      Language Bool) ∈ PvsNP.P := by
  obtain ⟨cs⟩ := sqrtStep_poly
  have hiter : PvsNP.PolyTimeComputable
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => sqrtStep^[p.2.length] p.1) :=
    Iter.iter_polyTime_measure sqrtStep cs sqrtMeasure 4
      sqrtMeasure_step sqrtStep_len sqrtMeasure_linear
  have hpow2 : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => pow2List x.length) :=
    cpt_app2 cpt_zeros (cpt_const [true])
  have hinit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => pairB (pairB x (pow2List x.length)) []) :=
    cpt_pairB2 (cpt_pairB2 cpt_id hpow2) (cpt_const [])
  have hrFinal : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString rFinal :=
    cpt_unpairB2_1
      (PvsNP.Units.m2_polytime_comp PvsNP.encodeString
        PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair PvsNP.encodeString
        _ _ (cpt_pair hinit hpow2) hiter)
  have hpairRR : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x => (rFinal x, rFinal x)) := by
    rw [← encodePair_eq, encodeString_eq]
    exact cpt_pair hrFinal hrFinal
  have hsqFinal : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x => Nat.bits (val (rFinal x) * val (rFinal x))) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun x => (rFinal x, rFinal x))
      (fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2))
      hpairRR PvsNP.Units.tf_fun_pair_mul
  have hpairXS : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x => (x, Nat.bits (val (rFinal x) * val (rFinal x)))) := by
    rw [← encodePair_eq, encodeString_eq]
    exact cpt_pair cpt_id hsqFinal
  have hdec : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer sqDecider :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeAnswer
      (fun x => (x, Nat.bits (val (rFinal x) * val (rFinal x))))
      (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2))
      hpairXS PvsNP.Units.m2_binary_le_polytime
  refine ⟨sqDecider, hdec, ?_⟩
  intro x
  change (∃ k : ℕ, val x = k ^ 2) ↔ sqDecider x = true
  have hhi0 : val x < (val [] + 2 ^ (x.length + 1)) * (val [] + 2 ^ (x.length + 1)) := by
    have hlt := val_lt_two_pow x
    have h1 : 2 ^ x.length ≤ 2 ^ (x.length + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ (x.length + 1) ≤ 2 ^ (x.length + 1) * 2 ^ (x.length + 1) := Nat.le_mul_self _
    simp only [val_nil, Nat.zero_add]
    omega
  have hres := sqrtStep_iter x x.length [] (by simp [val_nil]) hhi0
  have hrf_lo : val (rFinal x) * val (rFinal x) ≤ val x := by
    simpa [rFinal, pow2List_length] using hres.1
  have hrf_hi : val x < (val (rFinal x) + 1) * (val (rFinal x) + 1) := by
    simpa [rFinal, pow2List_length] using hres.2
  simp only [sqDecider, decide_eq_true_eq, val_bits]
  constructor
  · rintro ⟨k, hk⟩
    have hkeq : k = val (rFinal x) := by
      have hsq : k * k = val x := by rw [hk, sq]
      have h1 : val (rFinal x) * val (rFinal x) ≤ k * k := by omega
      have h2 : k * k < (val (rFinal x) + 1) * (val (rFinal x) + 1) := by omega
      nlinarith
    rw [hk, sq, hkeq]
  · intro hge
    refine ⟨val (rFinal x), ?_⟩
    rw [sq]
    omega

end PvsNP.Units.tl_lang_val_pow_p

theorem PvsNP.Units.tl_lang_val_pow_p :
    ({x : List Bool | ∃ k : ℕ, Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = k ^ 2} :
      Language Bool) ∈ PvsNP.P :=
  PvsNP.Units.tl_lang_val_pow_p.main_proof
