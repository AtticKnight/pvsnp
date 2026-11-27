import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_transducer_polytime
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_bool_combine_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_iterate_polytime
import PvsNP.Units.m2_p_rotate_closed
import PvsNP.Units.m2_take_drop_length_polytime
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.tf_fun_pair_add

set_option autoImplicit false

namespace PvsNP.Units.tr_rel_val_coprime

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

/-! ### Part 1: Binary values, `Nat.bits`, and two's-complement subtraction -/

def val (x : List Bool) : ℕ := Nat.ofDigits 2 (x.map Bool.toNat)

theorem val_cons (b : Bool) (xs : List Bool) :
    val (b :: xs) = b.toNat + 2 * val xs := by
  simp [val, Nat.ofDigits]

theorem val_append (u v : List Bool) :
    val (u ++ v) = val u + 2 ^ u.length * val v := by
  induction u with
  | nil => simp [val]
  | cons b xs ih =>
    simp only [List.cons_append, val_cons, ih, List.length_cons, pow_succ]
    ring

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
    · have hcond : n = 0 → b = true := by intro hn; cases b <;> simp_all
      rw [Nat.bits_append_bit n b hcond, val_cons, ih, Nat.bit_val]
      omega

theorem bits_eq_iff (m n : ℕ) : Nat.bits m = Nat.bits n ↔ m = n := by
  constructor
  · intro h
    have := congrArg val h
    rwa [val_bits, val_bits] at this
  · intro h; rw [h]

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

theorem val_map_false (u : List Bool) : val (u.map (fun _ => false)) = 0 := by
  induction u with
  | nil => simp [val]
  | cons _ xs ih => simp only [List.map_cons, val_cons, Bool.toNat_false, Nat.zero_add, ih, Nat.mul_zero]

theorem val_add_not (w : List Bool) : val w + val (w.map (!·)) + 1 = 2 ^ w.length := by
  induction w with
  | nil => simp [val]
  | cons b xs ih =>
    simp only [List.map_cons, val_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem val_take (l : List Bool) (k : ℕ) : val (l.take k) = val l % 2 ^ k := by
  by_cases hk : l.length ≤ k
  · rw [List.take_of_length_le hk]
    have hlt : val l < 2 ^ k := lt_of_lt_of_le (val_lt_two_pow l) (Nat.pow_le_pow_right (by decide) hk)
    exact (Nat.mod_eq_of_lt hlt).symm
  · have hlt : k ≤ l.length := by omega
    have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
    have hlen : (l.take k).length = k := List.length_take_of_le hlt
    have hvlt : val (l.take k) < 2 ^ k := by simpa only [hlen] using val_lt_two_pow (l.take k)
    conv_rhs => rw [hsplit, val_append, hlen]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hvlt]

theorem bits_eq_nil_iff (n : ℕ) : Nat.bits n = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := val_bits n
    rw [h] at hv
    exact hv.symm
  · intro h; subst h; rfl

theorem bits_tail_even {n : ℕ} (heven : n % 2 = 0) : (Nat.bits n).tail = Nat.bits (n / 2) := by
  by_cases h0 : n = 0
  · subst h0; rfl
  · have hq : n / 2 ≠ 0 := by omega
    have hbit : n = Nat.bit false (n / 2) := by rw [Nat.bit_val]; simp; omega
    conv_lhs => rw [hbit]
    rw [Nat.bits_append_bit (n / 2) false (fun h => absurd h hq), List.tail_cons]

theorem bits_take1_eq_false {n : ℕ} (h : (Nat.bits n).take 1 = [false]) : n % 2 = 0 ∧ n ≠ 0 := by
  cases hb : Nat.bits n with
  | nil => rw [hb] at h; simp at h
  | cons b xs =>
    rw [hb] at h
    simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at h
    subst h
    have hv := val_bits n
    rw [hb, val_cons] at hv
    simp only [Bool.toNat_false, Nat.zero_add] at hv
    refine ⟨by omega, ?_⟩
    intro h0
    subst h0
    simp at hb

theorem bits_take1_ne_false {n : ℕ} (hn : n ≠ 0) (h : (Nat.bits n).take 1 ≠ [false]) : n % 2 = 1 := by
  cases hb : Nat.bits n with
  | nil => exact absurd ((bits_eq_nil_iff n).1 hb) hn
  | cons b xs =>
    rw [hb] at h
    cases b with
    | false => exact absurd rfl h
    | true =>
      have hv := val_bits n
      rw [hb, val_cons] at hv
      simp at hv
      omega

/-! ### Part 2: Binary addition, canonicalization, and two's-complement subtraction -/

def binAdd (a b : List Bool) : List Bool := Nat.bits (val a + val b)

def canon (x : List Bool) : List Bool := binAdd x []

theorem canon_eq (x : List Bool) : canon x = Nat.bits (val x) := by
  simp [canon, binAdd, val]

theorem canon_length_le (x : List Bool) : (canon x).length ≤ x.length := by
  rw [canon_eq]
  exact bits_length_le_of_lt_two_pow (val_lt_two_pow x)

def padTake (u v : List Bool) : List Bool := (v ++ u.map (fun _ => false)).take u.length

def binSub (u v : List Bool) : List Bool :=
  canon ((binAdd (binAdd u ((padTake u v).map (!·))) [true]).take u.length)

theorem binSub_length_le (u v : List Bool) : (binSub u v).length ≤ u.length := by
  unfold binSub
  have h1 := canon_length_le ((binAdd (binAdd u ((padTake u v).map (!·))) [true]).take u.length)
  have h2 : ((binAdd (binAdd u ((padTake u v).map (!·))) [true]).take u.length).length ≤ u.length :=
    List.length_take_le _ _
  omega

theorem binSub_eq {m n : ℕ} (hle : n ≤ m) :
    binSub (Nat.bits m) (Nat.bits n) = Nat.bits (m - n) := by
  set u := Nat.bits m
  set v := Nat.bits n
  have hmlt : m < 2 ^ u.length := by rw [← val_bits m]; exact val_lt_two_pow u
  have hvle : v.length ≤ u.length := bits_length_le_of_lt_two_pow (by omega)
  have hpad : padTake u v = v ++ (u.take (u.length - v.length)).map (fun _ => false) := by
    simp only [padTake, List.take_append, List.take_of_length_le hvle, List.map_take]
  have hpadLen : (padTake u v).length = u.length := by
    simp only [padTake]
    apply List.length_take_of_le
    simp only [List.length_append, List.length_map]
    omega
  have hpadVal : val (padTake u v) = n := by
    rw [hpad, val_append, val_map_false, Nat.mul_zero, Nat.add_zero]
    exact val_bits n
  have hnot := val_add_not (padTake u v)
  rw [hpadVal, hpadLen] at hnot
  have hsum : val (binAdd (binAdd u ((padTake u v).map (!·))) [true]) = 2 ^ u.length + (m - n) := by
    simp only [binAdd, val_bits]
    have h1 : val [true] = 1 := rfl
    rw [val_bits m, h1]
    omega
  rw [binSub, canon_eq, val_take, hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-! ### Part 3: Polytime combinators -/

theorem cpt_zeroPad :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.map (fun _ => false)) := by
  refine PvsNP.Units.m2_transducer_polytime Unit (fun _ _ => ((), some false)) (fun _ => none)
    (fun _ l => l.map (fun _ => false)) ?_ ?_ ()
  · intro _; rfl
  · intro _ _ _; simp

theorem cpt_notBits :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.map (!·)) := by
  refine PvsNP.Units.m2_transducer_polytime Unit (fun _ b => ((), some (!b))) (fun _ => none)
    (fun _ l => l.map (!·)) ?_ ?_ ()
  · intro _; rfl
  · intro _ _ _; simp

theorem cpt_tailStr :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.tail) := by
  refine PvsNP.Units.m2_transducer_polytime Bool
    (fun seen b => if seen then (true, some b) else (true, none))
    (fun _ => none)
    (fun seen l => if seen then l else l.tail) ?_ ?_ false
  · intro q; cases q <;> rfl
  · intro q b x; cases q <;> simp

theorem cpt_binAdd_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => binAdd (f s) (g s)) :=
  cpt_comp (f := fun s => (f s, g s))
    (g := fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    (PvsNP.Units.m2_pair_build_polytime f g hf hg) PvsNP.Units.tf_fun_pair_add

theorem cpt_binLe_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun s => decide (val (f s) ≤ val (g s))) :=
  cpt_comp (f := fun s => (f s, g s))
    (g := fun p : List Bool × List Bool => decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    (PvsNP.Units.m2_pair_build_polytime f g hf hg) PvsNP.Units.m2_binary_le_polytime

theorem cpt_takeLen_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (g s).take (f s).length) :=
  cpt_comp (f := fun s => (f s, g s))
    (g := fun p : List Bool × List Bool => p.2.take p.1.length)
    (PvsNP.Units.m2_pair_build_polytime f g hf hg) PvsNP.Units.m2_take_drop_length_polytime.1

theorem cpt_eq_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun s => decide (f s = g s)) :=
  cpt_comp (PvsNP.Units.m2_pair_build_polytime f g hf hg) PvsNP.Units.m2_eq_polytime

theorem cpt_binSub_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => binSub (f s) (g s)) := by
  have hPad : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => padTake (f s) (g s)) :=
    cpt_takeLen_fun f (fun s => g s ++ (f s).map (fun _ => false))
      hf (cpt_app2 hg (cpt_comp hf cpt_zeroPad))
  have hInv : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (padTake (f s) (g s)).map (!·)) :=
    cpt_comp hPad cpt_notBits
  have hAdd1 := cpt_binAdd_fun _ _ hf hInv
  have hAdd2 := cpt_binAdd_fun _ _ hAdd1 (cpt_const [true])
  have hTk := cpt_takeLen_fun f _ hf hAdd2
  exact cpt_binAdd_fun _ _ hTk (cpt_const [])

/-! ### Part 4: Stein's binary GCD step and polytime proof -/

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

def gcdStep (s : List Bool) : List Bool :=
  if decide ((unpairB s).1 = []) || decide ((unpairB s).2 = []) then s
  else if decide ((unpairB s).1.take 1 = [false]) && decide ((unpairB s).2.take 1 = [false]) then pairB [] []
  else if decide ((unpairB s).1.take 1 = [false]) then pairB (unpairB s).1.tail (unpairB s).2
  else if decide ((unpairB s).2.take 1 = [false]) then pairB (unpairB s).1 (unpairB s).2.tail
  else if decide (val (unpairB s).1 ≤ val (unpairB s).2) then pairB (unpairB s).1 (binSub (unpairB s).2 (unpairB s).1).tail
  else pairB (binSub (unpairB s).1 (unpairB s).2).tail (unpairB s).2

theorem gcdStep_len (s : List Bool) : (gcdStep s).length ≤ s.length + 0 := by
  have hw := unpairB_weighted s
  unfold gcdStep
  split_ifs with h0 h1 h2 h3 h4
  · omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h0
    have ha : 1 ≤ (unpairB s).1.length := List.length_pos_of_ne_nil h0.1
    have hb : 1 ≤ (unpairB s).2.length := List.length_pos_of_ne_nil h0.2
    simp only [pairB_length, List.length_nil]
    omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h0
    have ha : 1 ≤ (unpairB s).1.length := List.length_pos_of_ne_nil h0.1
    simp only [pairB_length, List.length_tail]
    omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h0
    have hb : 1 ≤ (unpairB s).2.length := List.length_pos_of_ne_nil h0.2
    simp only [pairB_length, List.length_tail]
    omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h0
    have hb : 1 ≤ (unpairB s).2.length := List.length_pos_of_ne_nil h0.2
    have hsub := binSub_length_le (unpairB s).2 (unpairB s).1
    simp only [pairB_length, List.length_tail]
    omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h0
    have ha : 1 ≤ (unpairB s).1.length := List.length_pos_of_ne_nil h0.1
    have hsub := binSub_length_le (unpairB s).1 (unpairB s).2
    simp only [pairB_length, List.length_tail]
    omega

theorem cpt_gcdStep :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString gcdStep := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1_1 cpt_id
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  have hA0 := cpt_eq_fun _ _ hA (cpt_const [])
  have hB0 := cpt_eq_fun _ _ hB (cpt_const [])
  have hZero := PvsNP.Units.m2_bool_combine_polytime (· || ·) _ _ hA0 hB0
  have hAev := cpt_eq_fun _ _ (cpt_comp hA PvsNP.Units.m2_p_rotate_closed.cpt_take1) (cpt_const [false])
  have hBev := cpt_eq_fun _ _ (cpt_comp hB PvsNP.Units.m2_p_rotate_closed.cpt_take1) (cpt_const [false])
  have hBothEv := PvsNP.Units.m2_bool_combine_polytime (· && ·) _ _ hAev hBev
  have hLe := cpt_binLe_fun _ _ hA hB
  have hBrSubB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => pairB (unpairB s).1 (binSub (unpairB s).2 (unpairB s).1).tail) :=
    cpt_pairB2 hA (cpt_comp (cpt_binSub_fun _ _ hB hA) cpt_tailStr)
  have hBrSubA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => pairB (binSub (unpairB s).1 (unpairB s).2).tail (unpairB s).2) :=
    cpt_pairB2 (cpt_comp (cpt_binSub_fun _ _ hA hB) cpt_tailStr) hB
  have h5 := PvsNP.Units.m2_ite_polytime _ _ _ hLe hBrSubB hBrSubA
  have h4 := PvsNP.Units.m2_ite_polytime _ _ _ hBev (cpt_pairB2 hA (cpt_comp hB cpt_tailStr)) h5
  have h3 := PvsNP.Units.m2_ite_polytime _ _ _ hAev (cpt_pairB2 (cpt_comp hA cpt_tailStr) hB) h4
  have h2 := PvsNP.Units.m2_ite_polytime _ _ _ hBothEv (cpt_const (pairB [] [])) h3
  exact PvsNP.Units.m2_ite_polytime _ _ _ hZero cpt_id h2

/-! ### Part 5: Correctness and convergence of Stein's binary GCD -/

theorem gcdStep_canon (m n : ℕ) :
    ∃ m' n' : ℕ,
      gcdStep (pairB (Nat.bits m) (Nat.bits n)) = pairB (Nat.bits m') (Nat.bits n') ∧
      (Nat.gcd m' n' = 1 ↔ Nat.gcd m n = 1) ∧
      ((m = 0 ∨ n = 0) → (m' = 0 ∨ n' = 0)) ∧
      (m ≠ 0 → n ≠ 0 → (Nat.bits m').length + (Nat.bits n').length < (Nat.bits m).length + (Nat.bits n).length) := by
  unfold gcdStep
  simp only [unpairB_pairB]
  split_ifs with h0 h1 h2 h3 h4
  · refine ⟨m, n, rfl, Iff.rfl, id, ?_⟩
    intro hm hn
    simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff] at h0
    rcases h0 with rfl | rfl <;> contradiction
  · simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff, not_or] at h0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    have hme := (bits_take1_eq_false h1.1).1
    have hne := (bits_take1_eq_false h1.2).1
    refine ⟨0, 0, rfl, ?_, fun _ => Or.inl rfl, ?_⟩
    · have h2dvd : 2 ∣ Nat.gcd m n := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hme) (Nat.dvd_of_mod_eq_zero hne)
      have hne1 : Nat.gcd m n ≠ 1 := by
        intro hgcd
        rw [hgcd] at h2dvd
        omega
      simp [hne1]
    · intro hm hn
      have hpos1 : 1 ≤ (Nat.bits m).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff m).1 hm)
      have hpos2 : 1 ≤ (Nat.bits n).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff n).1 hn)
      have hz : (Nat.bits 0).length = 0 := rfl
      omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff, not_or] at h0
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h1
    simp only [decide_eq_true_eq] at h2
    have hme := (bits_take1_eq_false h2).1
    have hno := bits_take1_ne_false h0.2 (h1 h2)
    refine ⟨m / 2, n, by rw [bits_tail_even hme], ?_, fun h => by rcases h with rfl | rfl <;> simp at h0, ?_⟩
    · have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.2 (Nat.odd_iff.2 hno)
      have hm2 : m = 2 * (m / 2) := by omega
      conv_rhs => rw [hm2, Nat.Coprime.gcd_mul_left_cancel (m / 2) hcop]
    · intro hm _
      rw [← bits_tail_even hme, List.length_tail]
      have hpos1 : 1 ≤ (Nat.bits m).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff m).1 hm)
      omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff, not_or] at h0
    simp only [decide_eq_true_eq] at h2 h3
    have hne := (bits_take1_eq_false h3).1
    have hmo := bits_take1_ne_false h0.1 h2
    refine ⟨m, n / 2, by rw [bits_tail_even hne], ?_, fun h => by rcases h with rfl | rfl <;> simp at h0, ?_⟩
    · have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.2 (Nat.odd_iff.2 hmo)
      have hn2 : n = 2 * (n / 2) := by omega
      conv_rhs => rw [hn2, Nat.gcd_comm, Nat.Coprime.gcd_mul_left_cancel (n / 2) hcop, Nat.gcd_comm]
    · intro _ hn
      rw [← bits_tail_even hne, List.length_tail]
      have hpos2 : 1 ≤ (Nat.bits n).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff n).1 hn)
      omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff, not_or] at h0
    simp only [decide_eq_true_eq] at h2 h3 h4
    rw [val_bits, val_bits] at h4
    have hmo := bits_take1_ne_false h0.1 h2
    have hno := bits_take1_ne_false h0.2 h3
    have hde : (n - m) % 2 = 0 := by omega
    refine ⟨m, (n - m) / 2, by rw [binSub_eq h4, bits_tail_even hde], ?_,
      fun h => by rcases h with rfl | rfl <;> simp at h0, ?_⟩
    · have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.2 (Nat.odd_iff.2 hmo)
      have hsub_gcd : Nat.gcd m n = Nat.gcd m (n - m) := by
        have : n = (n - m) + m := by omega
        conv_lhs => rw [this, Nat.gcd_add_self_right]
      have hd2 : n - m = 2 * ((n - m) / 2) := by omega
      conv_rhs => rw [hsub_gcd, hd2, Nat.gcd_comm, Nat.Coprime.gcd_mul_left_cancel ((n - m) / 2) hcop, Nat.gcd_comm]
    · intro _ hn
      rw [← bits_tail_even hde, ← binSub_eq h4, List.length_tail]
      have hsub := binSub_length_le (Nat.bits n) (Nat.bits m)
      have hpos2 : 1 ≤ (Nat.bits n).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff n).1 hn)
      omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, bits_eq_nil_iff, not_or] at h0
    simp only [decide_eq_true_eq] at h2 h3 h4
    rw [val_bits, val_bits] at h4
    have hlt : n ≤ m := by omega
    have hmo := bits_take1_ne_false h0.1 h2
    have hno := bits_take1_ne_false h0.2 h3
    have hde : (m - n) % 2 = 0 := by omega
    refine ⟨(m - n) / 2, n, by rw [binSub_eq hlt, bits_tail_even hde], ?_,
      fun h => by rcases h with rfl | rfl <;> simp at h0, ?_⟩
    · have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.2 (Nat.odd_iff.2 hno)
      have hsub_gcd : Nat.gcd m n = Nat.gcd (m - n) n := by
        have : m = (m - n) + n := by omega
        conv_lhs => rw [this, Nat.gcd_add_self_left]
      have hd2 : m - n = 2 * ((m - n) / 2) := by omega
      conv_rhs => rw [hsub_gcd, hd2, Nat.Coprime.gcd_mul_left_cancel ((m - n) / 2) hcop]
    · intro hm _
      rw [← bits_tail_even hde, ← binSub_eq hlt, List.length_tail]
      have hsub := binSub_length_le (Nat.bits m) (Nat.bits n)
      have hpos1 : 1 ≤ (Nat.bits m).length := List.length_pos_of_ne_nil (mt (bits_eq_nil_iff m).1 hm)
      omega

theorem gcdStep_iter (t m n : ℕ) :
    ∃ m' n' : ℕ,
      gcdStep^[t] (pairB (Nat.bits m) (Nat.bits n)) = pairB (Nat.bits m') (Nat.bits n') ∧
      (Nat.gcd m' n' = 1 ↔ Nat.gcd m n = 1) ∧
      ((Nat.bits m).length + (Nat.bits n).length ≤ t → (m' = 0 ∨ n' = 0)) := by
  induction t generalizing m n with
  | zero =>
    refine ⟨m, n, rfl, Iff.rfl, fun h => ?_⟩
    have h1 : (Nat.bits m).length = 0 := by omega
    exact Or.inl ((bits_eq_nil_iff m).1 (List.eq_nil_of_length_eq_zero h1))
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨m1, n1, hstep, hgcd1, hzero1, hdec1⟩ := gcdStep_canon m n
    rw [hstep]
    obtain ⟨m2, n2, hiter, hgcd2, hterm2⟩ := ih m1 n1
    refine ⟨m2, n2, hiter, hgcd2.trans hgcd1, fun hle => ?_⟩
    by_cases hmn : m = 0 ∨ n = 0
    · have hmn1 : m1 = 0 ∨ n1 = 0 := hzero1 hmn
      have hstay : ∀ k a b : ℕ, (a = 0 ∨ b = 0) →
          gcdStep^[k] (pairB (Nat.bits a) (Nat.bits b)) = pairB (Nat.bits a) (Nat.bits b) := by
        intro k a b hab
        induction k with
        | zero => rfl
        | succ k ihk =>
          rw [Function.iterate_succ_apply]
          have hfix : gcdStep (pairB (Nat.bits a) (Nat.bits b)) = pairB (Nat.bits a) (Nat.bits b) := by
            unfold gcdStep
            simp only [unpairB_pairB]
            rcases hab with rfl | rfl <;> simp
          rw [hfix, ihk]
      rw [hstay t m1 n1 hmn1] at hiter
      have hpair := congrArg unpairB hiter
      simp only [unpairB_pairB, Prod.mk.injEq] at hpair
      rw [bits_eq_iff, bits_eq_iff] at hpair
      rcases hmn1 with h1 | h2
      · exact Or.inl (hpair.1.symm.trans h1)
      · exact Or.inr (hpair.2.symm.trans h2)
    · have hm0 : m ≠ 0 := fun h => hmn (Or.inl h)
      have hn0 : n ≠ 0 := fun h => hmn (Or.inr h)
      have hlt := hdec1 hm0 hn0
      exact hterm2 (by omega)

def coprimeStr (s : List Bool) : Bool :=
  let sf := gcdStep^[((unpairB s).1 ++ (unpairB s).2).length]
    (pairB (canon (unpairB s).1) (canon (unpairB s).2))
  decide (binAdd (unpairB sf).1 (unpairB sf).2 = [true])

def coprimeFn (p : List Bool × List Bool) : Bool :=
  coprimeStr (pairB p.1 p.2)

theorem cpt_coprimeFn :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer coprimeFn := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1_1 cpt_id
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  have hInit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => pairB (canon (unpairB s).1) (canon (unpairB s).2)) :=
    cpt_pairB2 (cpt_binAdd_fun _ _ hA (cpt_const [])) (cpt_binAdd_fun _ _ hB (cpt_const []))
  have hCnt : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => (unpairB s).1 ++ (unpairB s).2) :=
    cpt_app2 hA hB
  have hIter := PvsNP.Units.m2_iterate_polytime gcdStep 0 cpt_gcdStep gcdStep_len
  have hRun : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun s => gcdStep^[((unpairB s).1 ++ (unpairB s).2).length]
        (pairB (canon (unpairB s).1) (canon (unpairB s).2))) :=
    cpt_comp
      (f := fun s => (pairB (canon (unpairB s).1) (canon (unpairB s).2), (unpairB s).1 ++ (unpairB s).2))
      (g := fun p : List Bool × List Bool => gcdStep^[p.2.length] p.1)
      (PvsNP.Units.m2_pair_build_polytime _ _ hInit hCnt) hIter
  have hSum := cpt_binAdd_fun _ _ (cpt_unpairB1_1 hRun) (cpt_unpairB2_1 hRun)
  have hStr : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer coprimeStr :=
    cpt_eq_fun _ _ hSum (cpt_const [true])
  exact cpt_comp (f := fun p : List Bool × List Bool => pairB p.1 p.2) (g := coprimeStr)
    cpt_pairB hStr

theorem coprimeFn_spec (p : List Bool × List Bool) :
    (Nat.gcd (val p.1) (val p.2) = 1) ↔ coprimeFn p = true := by
  simp only [coprimeFn, coprimeStr, unpairB_pairB, canon_eq, decide_eq_true_eq]
  obtain ⟨m', n', hiter, hgcd, hterm⟩ := gcdStep_iter (p.1 ++ p.2).length (val p.1) (val p.2)
  rw [hiter, unpairB_pairB]
  have hlen1 := bits_length_le_of_lt_two_pow (val_lt_two_pow p.1)
  have hlen2 := bits_length_le_of_lt_two_pow (val_lt_two_pow p.2)
  have hzero : m' = 0 ∨ n' = 0 := hterm (by simp only [List.length_append]; omega)
  have hsum_eq : Nat.gcd m' n' = m' + n' := by
    rcases hzero with rfl | rfl <;> simp
  rw [← hgcd, hsum_eq]
  simp only [binAdd, val_bits]
  have h1 : ([true] : List Bool) = Nat.bits 1 := rfl
  rw [h1, bits_eq_iff]

end PvsNP.Units.tr_rel_val_coprime

/-- Testing whether the binary values of two strings are coprime takes polynomial time (TM2). -/
theorem PvsNP.Units.tr_rel_val_coprime :
    ∃ f : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (Nat.gcd (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat)) (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)) = 1) ↔
          f p = true :=
  ⟨PvsNP.Units.tr_rel_val_coprime.coprimeFn,
   PvsNP.Units.tr_rel_val_coprime.cpt_coprimeFn,
   PvsNP.Units.tr_rel_val_coprime.coprimeFn_spec⟩
