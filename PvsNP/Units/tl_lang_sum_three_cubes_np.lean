import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_pair_fun_specialize
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_tm_self_delimiting_pair
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.tf_fun_pair_mul
import PvsNP.Units.tf_fun_pair_add

namespace PvsNP.Units.tl_lang_sum_three_cubes_np

private def val (l : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (l.map Bool.toNat)

private def encPair (u v : List Bool) : List Bool :=
  List.replicate u.length true ++ false :: (u ++ v)

private def decPair (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
    ((s.dropWhile id).tail).drop (s.takeWhile id).length)

private theorem takeWhile_rep_false (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).takeWhile id = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, List.takeWhile_cons, id_eq, ite_true, ih]

private theorem dropWhile_rep_false (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).dropWhile id = false :: r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, List.dropWhile_cons, id_eq, ite_true, ih]

private theorem decPair_encPair (u v : List Bool) : decPair (encPair u v) = (u, v) := by
  simp only [decPair, encPair, takeWhile_rep_false, dropWhile_rep_false, List.tail_cons,
    List.length_replicate, List.take_left, List.drop_left]

private theorem encPair_length (u v : List Bool) :
    (encPair u v).length = 2 * u.length + 1 + v.length := by
  simp only [encPair, List.length_append, List.length_replicate, List.length_cons]
  omega

private theorem val_cons (b : Bool) (l : List Bool) :
    val (b :: l) = b.toNat + 2 * val l := by
  simp only [val, List.map_cons, Nat.ofDigits_cons]

private theorem val_lt_two_pow : ∀ l : List Bool, val l < 2 ^ l.length
  | [] => by decide
  | b :: l => by
    have ih := val_lt_two_pow l
    rw [val_cons, List.length_cons, pow_succ']
    cases b
    · simp only [Bool.toNat_false]; omega
    · simp only [Bool.toNat_true]; omega

private theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => rfl
    | succ m =>
      set b : Bool := decide ((m + 1) % 2 = 1)
      set q : ℕ := (m + 1) / 2
      have hbit : m + 1 = Nat.bit b q := by
        cases hb : b
        · have : ¬ ((m + 1) % 2 = 1) := of_decide_eq_false hb
          change m + 1 = 2 * q; omega
        · have : (m + 1) % 2 = 1 := of_decide_eq_true hb
          change m + 1 = 2 * q + 1; omega
      have hcond : q = 0 → b = true := by
        intro hq; exact decide_eq_true (by omega)
      have hlt : q < m + 1 := by omega
      rw [hbit, Nat.bits_append_bit q b hcond, val_cons, ih q hlt]
      rw [← hbit]
      cases hb : b
      · have : ¬ ((m + 1) % 2 = 1) := of_decide_eq_false hb
        simp only [Bool.toNat_false]; omega
      · have : (m + 1) % 2 = 1 := of_decide_eq_true hb
        simp only [Bool.toNat_true]; omega

private theorem bits_length_le : ∀ (k n : ℕ), n < 2 ^ k → (Nat.bits n).length ≤ k
  | 0, n, hn => by
    have h0 : n = 0 := by omega
    subst h0
    exact Nat.le_refl 0
  | k + 1, n, hn => by
    cases n with
    | zero => exact Nat.zero_le (k + 1)
    | succ m =>
      set b : Bool := decide ((m + 1) % 2 = 1)
      set q : ℕ := (m + 1) / 2
      have hbit : m + 1 = Nat.bit b q := by
        cases hb : b
        · have : ¬ ((m + 1) % 2 = 1) := of_decide_eq_false hb
          change m + 1 = 2 * q; omega
        · have : (m + 1) % 2 = 1 := of_decide_eq_true hb
          change m + 1 = 2 * q + 1; omega
      have hcond : q = 0 → b = true := by
        intro hq; exact decide_eq_true (by omega)
      rw [hbit, Nat.bits_append_bit q b hcond, List.length_cons]
      have hqlt : q < 2 ^ k := by rw [pow_succ'] at hn; omega
      have := bits_length_le k q hqlt
      omega

private theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f g : α → β} (h : PvsNP.PolyTimeComputable ea eb f) (heq : ∀ x, f x = g x) :
    PvsNP.PolyTimeComputable ea eb g := by
  obtain rfl : f = g := funext heq
  exact h

private def sq (u : List Bool) : List Bool :=
  Nat.bits (val u * val u)

private theorem cpt_sq : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sq :=
  cpt_congr
    (PvsNP.Units.m2_pair_fun_specialize
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
      [] PvsNP.Units.tf_fun_pair_mul).2.2
    (fun _ => rfl)

private def cube (u : List Bool) : List Bool :=
  Nat.bits (val u * val (sq u))

private theorem cpt_cube : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString cube := by
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun u : List Bool => u) :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  exact cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun u : List Bool => (u, sq u))
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
      (PvsNP.Units.m2_pair_build_polytime (fun u : List Bool => u) sq hid cpt_sq)
      PvsNP.Units.tf_fun_pair_mul)
    (fun _ => by simp only [Function.comp_apply, cube, val])

private theorem val_cube (u : List Bool) : val (cube u) = val u ^ 3 := by
  rw [cube, val_bits, sq, val_bits]
  ring

private def sumTwoCubes (w : List Bool) : List Bool :=
  Nat.bits (val (cube (decPair w).1) + val (cube (decPair w).2))

private theorem cpt_sumTwoCubes : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sumTwoCubes := by
  have hdec : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair decPair :=
    PvsNP.Units.m2_tm_self_delimiting_pair.2
  have h1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodePair
    decPair (fun p : List Bool × List Bool => (cube p.1, cube p.2))
    hdec (PvsNP.Units.m2_prod_map_polytime cube cube cpt_cube cpt_cube)
  have h2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    ((fun p : List Bool × List Bool => (cube p.1, cube p.2)) ∘ decPair)
    (fun p : List Bool × List Bool =>
      Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    h1 PvsNP.Units.tf_fun_pair_add
  exact cpt_congr h2 (fun _ => by simp only [Function.comp_apply, sumTwoCubes, val])

private def sumThreeCubes (w : List Bool) : List Bool :=
  Nat.bits (val (cube (decPair w).1) + val (sumTwoCubes (decPair w).2))

private theorem cpt_sumThreeCubes : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sumThreeCubes := by
  have hdec : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair decPair :=
    PvsNP.Units.m2_tm_self_delimiting_pair.2
  have h1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodePair
    decPair (fun p : List Bool × List Bool => (cube p.1, sumTwoCubes p.2))
    hdec (PvsNP.Units.m2_prod_map_polytime cube sumTwoCubes cpt_cube cpt_sumTwoCubes)
  have h2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
    ((fun p : List Bool × List Bool => (cube p.1, sumTwoCubes p.2)) ∘ decPair)
    (fun p : List Bool × List Bool =>
      Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    h1 PvsNP.Units.tf_fun_pair_add
  exact cpt_congr h2 (fun _ => by simp only [Function.comp_apply, sumThreeCubes, val])

private theorem val_sumThreeCubes (w : List Bool) :
    val (sumThreeCubes w) =
      val (decPair w).1 ^ 3 + val (decPair (decPair w).2).1 ^ 3 + val (decPair (decPair w).2).2 ^ 3 := by
  rw [sumThreeCubes, val_bits, val_cube, sumTwoCubes, val_bits, val_cube, val_cube]
  ring

private def binLE (p : List Bool × List Bool) : Bool :=
  decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))

private def pairSum (p : List Bool × List Bool) : List Bool × List Bool :=
  (p.1, sumThreeCubes p.2)

private def verifier (p : List Bool × List Bool) : Bool :=
  (binLE ∘ pairSum) p && (binLE ∘ ((fun q : List Bool × List Bool => (q.2, q.1)) ∘ pairSum)) p

private theorem cpt_verifier : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer verifier := by
  have hid : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x) :=
    ⟨Turing.idComputableInPolyTime PvsNP.encodeString⟩
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair pairSum :=
    PvsNP.Units.m2_prod_map_polytime (fun x : List Bool => x) sumThreeCubes hid cpt_sumThreeCubes
  have hle : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer binLE :=
    PvsNP.Units.m2_binary_le_polytime
  have hle1 := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    pairSum binLE hpair hle
  have hswap := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodePair
    pairSum (fun q : List Bool × List Bool => (q.2, q.1)) hpair PvsNP.Units.m2_tm_pair_swap_polytime
  have hle2 := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    ((fun q : List Bool × List Bool => (q.2, q.1)) ∘ pairSum) binLE hswap hle
  exact PvsNP.Units.m2_tm_pair_bool_combine (· && ·) _ _ hle1 hle2

private theorem binLE_eq_true (a b : List Bool) : binLE (a, b) = true ↔ val a ≤ val b :=
  decide_eq_true_iff

private theorem verifier_eq (x w : List Bool) :
    verifier (x, w) = (binLE (x, sumThreeCubes w) && binLE (sumThreeCubes w, x)) := by
  simp only [verifier, Function.comp_apply, pairSum]

private theorem verifier_iff (x w : List Bool) :
    verifier (x, w) = true ↔ val x = val (sumThreeCubes w) := by
  rw [verifier_eq, Bool.and_eq_true, binLE_eq_true, binLE_eq_true]
  omega

end PvsNP.Units.tl_lang_sum_three_cubes_np

theorem PvsNP.Units.tl_lang_sum_three_cubes_np :
    ({x : List Bool | ∃ a b c : ℕ, a ^ 3 + b ^ 3 + c ^ 3 = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.NP := by
  refine ⟨PvsNP.Units.tl_lang_sum_three_cubes_np.verifier,
    Polynomial.C 5 * Polynomial.X + Polynomial.C 2,
    PvsNP.Units.tl_lang_sum_three_cubes_np.cpt_verifier, fun x => ?_⟩
  constructor
  · rintro ⟨a, b, c, habc⟩
    have hxlt : PvsNP.Units.tl_lang_sum_three_cubes_np.val x < 2 ^ x.length :=
      PvsNP.Units.tl_lang_sum_three_cubes_np.val_lt_two_pow x
    have ha_le : a ≤ a ^ 3 := Nat.le_self_pow (by decide) a
    have hb_le : b ≤ b ^ 3 := Nat.le_self_pow (by decide) b
    have hc_le : c ≤ c ^ 3 := Nat.le_self_pow (by decide) c
    have halt : a < 2 ^ x.length := by
      change a ^ 3 + b ^ 3 + c ^ 3 = PvsNP.Units.tl_lang_sum_three_cubes_np.val x at habc; omega
    have hblt : b < 2 ^ x.length := by
      change a ^ 3 + b ^ 3 + c ^ 3 = PvsNP.Units.tl_lang_sum_three_cubes_np.val x at habc; omega
    have hclt : c < 2 ^ x.length := by
      change a ^ 3 + b ^ 3 + c ^ 3 = PvsNP.Units.tl_lang_sum_three_cubes_np.val x at habc; omega
    have halen := PvsNP.Units.tl_lang_sum_three_cubes_np.bits_length_le x.length a halt
    have hblen := PvsNP.Units.tl_lang_sum_three_cubes_np.bits_length_le x.length b hblt
    have hclen := PvsNP.Units.tl_lang_sum_three_cubes_np.bits_length_le x.length c hclt
    refine ⟨PvsNP.Units.tl_lang_sum_three_cubes_np.encPair (Nat.bits a)
      (PvsNP.Units.tl_lang_sum_three_cubes_np.encPair (Nat.bits b) (Nat.bits c)), ?_, ?_⟩
    · rw [PvsNP.Units.tl_lang_sum_three_cubes_np.encPair_length,
        PvsNP.Units.tl_lang_sum_three_cubes_np.encPair_length]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      omega
    · rw [PvsNP.Units.tl_lang_sum_three_cubes_np.verifier_iff,
        PvsNP.Units.tl_lang_sum_three_cubes_np.val_sumThreeCubes,
        PvsNP.Units.tl_lang_sum_three_cubes_np.decPair_encPair,
        PvsNP.Units.tl_lang_sum_three_cubes_np.decPair_encPair,
        PvsNP.Units.tl_lang_sum_three_cubes_np.val_bits,
        PvsNP.Units.tl_lang_sum_three_cubes_np.val_bits,
        PvsNP.Units.tl_lang_sum_three_cubes_np.val_bits]
      exact habc.symm
  · rintro ⟨w, -, hw⟩
    rw [PvsNP.Units.tl_lang_sum_three_cubes_np.verifier_iff,
      PvsNP.Units.tl_lang_sum_three_cubes_np.val_sumThreeCubes] at hw
    exact ⟨PvsNP.Units.tl_lang_sum_three_cubes_np.val (PvsNP.Units.tl_lang_sum_three_cubes_np.decPair w).1,
      PvsNP.Units.tl_lang_sum_three_cubes_np.val (PvsNP.Units.tl_lang_sum_three_cubes_np.decPair (PvsNP.Units.tl_lang_sum_three_cubes_np.decPair w).2).1,
      PvsNP.Units.tl_lang_sum_three_cubes_np.val (PvsNP.Units.tl_lang_sum_three_cubes_np.decPair (PvsNP.Units.tl_lang_sum_three_cubes_np.decPair w).2).2,
      hw.symm⟩
