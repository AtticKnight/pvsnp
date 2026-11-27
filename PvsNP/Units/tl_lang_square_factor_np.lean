import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.tf_fun_pair_add
import PvsNP.Units.tf_fun_pair_mul

namespace PvsNP.Units.tl_lang_square_factor_np

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def val (s : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (s.map Bool.toNat)

theorem val_cons (b : Bool) (s : List Bool) : val (b :: s) = b.toNat + 2 * val s := by
  simp [val, Nat.ofDigits_cons]

theorem val_lt_two_pow (s : List Bool) : val s < 2 ^ s.length := by
  induction s with
  | nil => simp [val]
  | cons b t ih =>
    simp only [val_cons, List.length_cons, pow_succ]
    cases b
    · simp
      omega
    · simp
      omega

theorem ofDigits_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero => simp [val]
  | bit b m ih =>
    by_cases h : b = false ∧ m = 0
    · rcases h with ⟨rfl, rfl⟩
      simp [val]
    · have hne : m = 0 → b = true := by
        intro hm
        cases b
        · exact absurd ⟨rfl, hm⟩ h
        · rfl
      rw [Nat.bits_append_bit m b hne]
      simp only [val_cons, ih]
      cases b
      · simp [Nat.bit]
      · simp [Nat.bit]
        ring

def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => decide (n % 2 = 1) :: toBits k (n / 2)

theorem toBits_length (k n : ℕ) : (toBits k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [toBits, ih]

theorem val_toBits (k n : ℕ) (hn : n < 2 ^ k) : val (toBits k n) = n := by
  induction k generalizing n with
  | zero =>
    simp at hn
    subst hn
    rfl
  | succ k ih =>
    have hdiv : n / 2 < 2 ^ k := by
      rw [pow_succ] at hn
      omega
    simp only [toBits, val_cons, ih (n / 2) hdiv]
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · simp only [h0, Nat.zero_ne_one, decide_false, Bool.toNat_false, Nat.zero_add]
      omega
    · simp only [h1, decide_true, Bool.toNat_true]
      omega

theorem bits_tail_ne_nil_iff (n : ℕ) : (Nat.bits n).tail ≠ [] ↔ 1 < n := by
  constructor
  · intro hne
    by_contra hle
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl
    · exact hne rfl
    · exact hne rfl
  · intro hgt hnil
    have hlen : (Nat.bits n).length ≤ 1 := by
      cases h : Nat.bits n with
      | nil => simp
      | cons _ t =>
        rw [h] at hnil
        simp at hnil
        subst hnil
        simp
    have hlt := val_lt_two_pow (Nat.bits n)
    rw [ofDigits_bits] at hlt
    have h2 : 2 ^ (Nat.bits n).length ≤ 2 := by
      have : 2 ^ (Nat.bits n).length ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hlen
      simpa using this
    omega

def isNonEmptyδ : Bool → Bool → Bool × Option Bool
  | _, _ => (true, none)

def isNonEmptyFin : Bool → Option Bool
  | false => some false
  | true => some true

theorem isNonEmpty_run (x : List Bool) (q : Bool) :
    fstRun isNonEmptyδ isNonEmptyFin q x =
      Computability.encodeBool (if q then true else decide (x ≠ [])) := by
  induction x generalizing q with
  | nil => cases q <;> rfl
  | cons _ t ih =>
    simp only [fstRun, isNonEmptyδ, Option.toList_none, List.nil_append]
    rw [ih true]
    cases q <;> rfl

theorem cpt_isNonEmpty :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun x : List Bool => decide (x ≠ [])) := by
  refine fst_polyTime (fun x : List Bool => x) Computability.encodeBool
    (fun x : List Bool => decide (x ≠ [])) isNonEmptyδ isNonEmptyFin false ?_
  intro x
  simpa using (isNonEmpty_run x false).symm

theorem encodePair_eq : PvsNP.encodePair = PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair := by
  funext ⟨x, y⟩
  simp [PvsNP.encodePair, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair,
    Computability.encodingProd, Computability.encodingList]

theorem cpt_canonBits :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => Nat.bits (val x)) := by
  have hadd : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => Nat.bits (val p.1 + val p.2)) := by
    rw [← encodePair_eq]
    exact PvsNP.Units.tf_fun_pair_add
  have hc := cpt_comp (cpt_pair cpt_id (cpt_const [])) hadd
  have hfun : (fun a : List Bool => Nat.bits (val a + val [])) =
      (fun x : List Bool => Nat.bits (val x)) := by
    funext x
    simp [val]
  change ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
    (fun a : List Bool => Nat.bits (val a + val [])) at hc
  rw [hfun] at hc
  exact hc

theorem cpt_mulBits :
    ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => Nat.bits (val p.1 * val p.2)) := by
  rw [← encodePair_eq]
  exact PvsNP.Units.tf_fun_pair_mul

def lhsSF (x : List Bool) : List Bool :=
  pairB (Nat.bits (val x)) [true]

def rhsSF (cert : List Bool) : List Bool :=
  let sd := (unpairB cert).1
  let sq := (unpairB cert).2
  pairB (Nat.bits (val sd * val sd * val sq))
    (if decide ((Nat.bits (val sd)).tail ≠ []) then [true] else [])

theorem cpt_lhsSF :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) lhsSF := by
  unfold lhsSF
  exact cpt_pairB2 cpt_canonBits (cpt_const [true])

theorem cpt_rhsSF :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) rhsSF := by
  have hsd := cpt_unpairB1
  have hsq := cpt_unpairB2
  have hd2 := cpt_comp (cpt_pair hsd hsd) cpt_mulBits
  have hprod0 := cpt_comp (cpt_pair hd2 hsq) cpt_mulBits
  have hprod : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun cert : List Bool => Nat.bits (val (unpairB cert).1 * val (unpairB cert).1 * val (unpairB cert).2)) := by
    have hfun : (fun a : List Bool =>
          Nat.bits (val (Nat.bits (val (unpairB a).1 * val (unpairB a).1)) * val (unpairB a).2)) =
        (fun cert : List Bool =>
          Nat.bits (val (unpairB cert).1 * val (unpairB cert).1 * val (unpairB cert).2)) := by
      funext cert
      rw [ofDigits_bits]
    change ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun a : List Bool =>
        Nat.bits (val (Nat.bits (val (unpairB a).1 * val (unpairB a).1)) * val (unpairB a).2)) at hprod0
    rw [hfun] at hprod0
    exact hprod0
  have hdBits : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun cert : List Bool => (Nat.bits (val (unpairB cert).1)).tail) :=
    cpt_tail1 (cpt_comp (f := fun cert : List Bool => (unpairB cert).1)
      (g := fun x : List Bool => Nat.bits (val x)) hsd cpt_canonBits)
  have hgt1Bool : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun cert : List Bool => decide ((Nat.bits (val (unpairB cert).1)).tail ≠ [])) :=
    cpt_comp (f := fun cert : List Bool => (Nat.bits (val (unpairB cert).1)).tail)
      (g := fun l : List Bool => decide (l ≠ [])) hdBits cpt_isNonEmpty
  have hgt1Flag := cpt_bitFlag hgt1Bool
  unfold rhsSF
  exact cpt_pairB2 hprod hgt1Flag

theorem cpt_eq_pair (f1 f2 : List Bool → List Bool)
    (h1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f1)
    (h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f2) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => decide (f1 p.1 = f2 p.2)) := by
  have hboth : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun p : List Bool × List Bool => (f1 p.1, f2 p.2)) :=
    cpt_comp (cpt_first h1) (cpt_second h2)
  have heq : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (fun q : List Bool × List Bool => decide (q.1 = q.2)) := by
    rw [← encodePair_eq]
    exact PvsNP.Units.m2_eq_polytime
  have hres : ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool (fun p : List Bool × List Bool => decide (f1 p.1 = f2 p.2)) :=
    cpt_comp hboth heq
  rw [encodePair_eq]
  exact hres

theorem square_factor_np_aux :
    ({x : List Bool | ∃ d : ℕ, 1 < d ∧ d ^ 2 ∣ Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} :
      Language Bool) ∈ PvsNP.NP := by
  let Q : Polynomial ℕ := Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  refine ⟨fun p => decide (lhsSF p.1 = rhsSF p.2), Q,
    cpt_eq_pair lhsSF rhsSF cpt_lhsSF cpt_rhsSF, fun x => ?_⟩
  change (∃ d : ℕ, 1 < d ∧ d ^ 2 ∣ val x) ↔
    ∃ cert : List Bool, cert.length ≤ Q.eval x.length ∧ decide (lhsSF x = rhsSF cert) = true
  constructor
  · rintro ⟨d, hd, q, hq⟩
    have hxlt : val x < 2 ^ x.length := val_lt_two_pow x
    have hpick : ∃ d' q' : ℕ, 1 < d' ∧ val x = d' * d' * q' ∧
        d' < 2 ^ (x.length + 2) ∧ q' < 2 ^ x.length := by
      by_cases hx0 : val x = 0
      · refine ⟨2, 0, by omega, by simp [hx0], ?_, Nat.two_pow_pos _⟩
        have h4 : 2 ^ 2 ≤ 2 ^ (x.length + 2) := Nat.pow_le_pow_right (by omega) (by omega)
        have : 2 ^ 2 = 4 := by norm_num
        omega
      · have hqpos : 1 ≤ q := by
          cases q with
          | zero => simp at hq; exact absurd hq hx0
          | succ _ => omega
        have hd_le : d ≤ val x := by
          have h1 : d ≤ d * d := Nat.le_mul_of_pos_right d (by omega)
          have h2 : d * d ≤ d * d * q := Nat.le_mul_of_pos_right _ hqpos
          rw [hq, pow_two]
          omega
        have hq_le : q ≤ val x := by
          have h1 : 1 ≤ d ^ 2 := by
            rw [pow_two]
            exact Nat.mul_pos (by omega) (by omega)
          have h2 : q ≤ d ^ 2 * q := Nat.le_mul_of_pos_left q h1
          omega
        have h2pow : 2 ^ x.length ≤ 2 ^ (x.length + 2) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        refine ⟨d, q, hd, by rw [hq, pow_two], by omega, by omega⟩
    obtain ⟨d', q', hd', hprod, hdlt, hqlt⟩ := hpick
    let sd := toBits (x.length + 2) d'
    let sq := toBits x.length q'
    refine ⟨pairB sd sq, ?_, ?_⟩
    · simp only [pairB_length, sd, sq, toBits_length, Q, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      omega
    · simp only [decide_eq_true_eq, lhsSF, rhsSF, unpairB_pairB]
      have hsd : val sd = d' := val_toBits (x.length + 2) d' hdlt
      have hsq : val sq = q' := val_toBits x.length q' hqlt
      rw [hsd, hsq, ← hprod]
      have htail : (Nat.bits d').tail ≠ [] := (bits_tail_ne_nil_iff d').2 hd'
      simp [htail]
  · rintro ⟨cert, _, hacc⟩
    have heq : lhsSF x = rhsSF cert := of_decide_eq_true hacc
    dsimp only [lhsSF, rhsSF] at heq
    have hpair := congrArg unpairB heq
    simp only [unpairB_pairB, Prod.mk.injEq] at hpair
    obtain ⟨hbits, hflag⟩ := hpair
    let d := val (unpairB cert).1
    let q := val (unpairB cert).2
    have hvalEq : val x = d * d * q := by
      have h := congrArg val hbits
      rw [ofDigits_bits, ofDigits_bits] at h
      exact h
    have hd : 1 < d := by
      rw [← bits_tail_ne_nil_iff d]
      by_contra hnil
      simp only [d] at hnil
      simp [hnil] at hflag
    refine ⟨d, hd, q, ?_⟩
    rw [pow_two]
    exact hvalEq

end PvsNP.Units.tl_lang_square_factor_np

/-- Binary strings whose numerical value is divisible by a square `d^2` with `d > 1` are in NP. -/
theorem PvsNP.Units.tl_lang_square_factor_np :
    ({x : List Bool | ∃ d : ℕ, 1 < d ∧ d ^ 2 ∣ Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} :
      Language Bool) ∈ PvsNP.NP :=
  PvsNP.Units.tl_lang_square_factor_np.square_factor_np_aux
