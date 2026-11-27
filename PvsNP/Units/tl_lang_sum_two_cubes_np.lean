import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_pair_fun_specialize
import PvsNP.Units.m2_prod_map_polytime
import PvsNP.Units.m2_tm_self_delimiting_pair
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.tf_fun_pair_mul
import PvsNP.Units.tf_fun_pair_add

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_sum_two_cubes_np

def val (l : List Bool) : ℕ :=
  Nat.ofDigits (2 : ℕ) (l.map Bool.toNat)

def encPair (u v : List Bool) : List Bool :=
  List.replicate u.length true ++ false :: (u ++ v)

def decPair (s : List Bool) : List Bool × List Bool :=
  (((s.dropWhile id).tail).take (s.takeWhile id).length,
    ((s.dropWhile id).tail).drop (s.takeWhile id).length)

theorem takeWhile_rep_false (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).takeWhile id = List.replicate n true := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem dropWhile_rep_false (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).dropWhile id = false :: r := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem decPair_encPair (u v : List Bool) : decPair (encPair u v) = (u, v) := by
  simp only [decPair, encPair, takeWhile_rep_false, dropWhile_rep_false, List.tail_cons,
    List.length_replicate, List.take_left, List.drop_left]

theorem encPair_length (u v : List Bool) :
    (encPair u v).length = 2 * u.length + 1 + v.length := by
  simp only [encPair, List.length_append, List.length_replicate, List.length_cons]
  omega

theorem val_lt_two_pow : ∀ l : List Bool, val l < 2 ^ l.length
  | [] => by simp [val]
  | b :: l => by
    have ih := val_lt_two_pow l
    have hcons : val (b :: l) = b.toNat + 2 * val l := rfl
    rw [hcons, List.length_cons, pow_succ']
    cases b <;> simp <;> omega

theorem val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit0_bits m (by omega)]
        have hcons : val (false :: Nat.bits m) = 0 + 2 * val (Nat.bits m) := rfl
        rw [hcons, ih m (by omega)]
        omega
    · rw [Nat.bit1_bits m]
      have hcons : val (true :: Nat.bits m) = 1 + 2 * val (Nat.bits m) := rfl
      rw [hcons, ih m (by omega)]
      omega

theorem bits_length_le : ∀ (k n : ℕ), n < 2 ^ k → (Nat.bits n).length ≤ k
  | 0, n, hn => by
    have h0 : n = 0 := by omega
    subst h0
    simp
  | k + 1, n, hn => by
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · rw [Nat.bit0_bits m (by omega), List.length_cons]
        have hm' : m < 2 ^ k := by rw [pow_succ'] at hn; omega
        have := bits_length_le k m hm'
        omega
    · rw [Nat.bit1_bits m, List.length_cons]
      have hm' : m < 2 ^ k := by rw [pow_succ'] at hn; omega
      have := bits_length_le k m hm'
      omega

private theorem cpt_congr {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f g : α → β} (h : PvsNP.PolyTimeComputable ea eb f) (heq : ∀ x, f x = g x) :
    PvsNP.PolyTimeComputable ea eb g := by
  obtain rfl : f = g := funext heq
  exact h

def sq (u : List Bool) : List Bool :=
  Nat.bits (val u * val u)

theorem cpt_sq : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sq :=
  cpt_congr
    (PvsNP.Units.m2_pair_fun_specialize
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
      [] PvsNP.Units.tf_fun_pair_mul).2.2
    (fun _ => by simp only [sq, val])

def cube (u : List Bool) : List Bool :=
  Nat.bits (val u * val (sq u))

theorem cpt_cube : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString cube :=
  cpt_congr
    (PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      (fun u : List Bool => (u, sq u))
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
      (PvsNP.Units.m2_pair_build_polytime (fun u : List Bool => u) sq
        PvsNP.Units.m2_prod_map_polytime.ident cpt_sq)
      PvsNP.Units.tf_fun_pair_mul)
    (fun _ => by simp only [Function.comp_apply, cube, val])

theorem val_cube (u : List Bool) : val (cube u) = val u ^ 3 := by
  rw [cube, val_bits, sq, val_bits]
  ring

def sumCubes (w : List Bool) : List Bool :=
  Nat.bits (val (cube (decPair w).1) + val (cube (decPair w).2))

theorem cpt_sumCubes : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sumCubes := by
  have hdec : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair decPair :=
    cpt_congr PvsNP.Units.m2_tm_self_delimiting_pair.2 (fun _ => by simp only [decPair])
  have h1 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodePair
      decPair (fun p : List Bool × List Bool => (cube p.1, cube p.2))
      hdec (PvsNP.Units.m2_prod_map_polytime cube cube cpt_cube cpt_cube)
  have h2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodePair PvsNP.encodeString
      ((fun p : List Bool × List Bool => (cube p.1, cube p.2)) ∘ decPair)
      (fun p : List Bool × List Bool =>
        Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
      h1 PvsNP.Units.tf_fun_pair_add
  exact cpt_congr h2 (fun _ => by simp only [Function.comp_apply, sumCubes, val])

theorem val_sumCubes (w : List Bool) :
    val (sumCubes w) = val (decPair w).1 ^ 3 + val (decPair w).2 ^ 3 := by
  rw [sumCubes, val_bits, val_cube, val_cube]

def binLE (p : List Bool × List Bool) : Bool :=
  decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat))

def pairSum (p : List Bool × List Bool) : List Bool × List Bool :=
  (p.1, sumCubes p.2)

def verifier (p : List Bool × List Bool) : Bool :=
  (binLE ∘ pairSum) p && (binLE ∘ ((fun q : List Bool × List Bool => (q.2, q.1)) ∘ pairSum)) p

theorem cpt_verifier : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer verifier := by
  have hpair : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodePair pairSum :=
    PvsNP.Units.m2_prod_map_polytime (fun x : List Bool => x) sumCubes
      PvsNP.Units.m2_prod_map_polytime.ident cpt_sumCubes
  have hle : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer binLE :=
    PvsNP.Units.m2_binary_le_polytime
  have hle1 := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    pairSum binLE hpair hle
  have hswap := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodePair
    pairSum (fun q : List Bool × List Bool => (q.2, q.1)) hpair PvsNP.Units.m2_tm_pair_swap_polytime
  have hle2 := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    ((fun q : List Bool × List Bool => (q.2, q.1)) ∘ pairSum) binLE hswap hle
  exact PvsNP.Units.m2_tm_pair_bool_combine (· && ·) _ _ hle1 hle2

theorem binLE_eq_true (a b : List Bool) : binLE (a, b) = true ↔ val a ≤ val b :=
  decide_eq_true_iff

theorem verifier_eq (x w : List Bool) :
    verifier (x, w) = (binLE (x, sumCubes w) && binLE (sumCubes w, x)) := by
  simp only [verifier, Function.comp_apply, pairSum]

theorem verifier_iff (x w : List Bool) :
    verifier (x, w) = true ↔ val x = val (sumCubes w) := by
  rw [verifier_eq, Bool.and_eq_true, binLE_eq_true, binLE_eq_true]
  omega

end PvsNP.Units.tl_lang_sum_two_cubes_np

/-- The strings whose binary value is a sum of two cubes are in NP (TM2): witness `a` and `b`
in binary inside a self-delimiting pair, cube both using `tf_fun_pair_mul`, sum with
`tf_fun_pair_add`, and compare equality with `x` via `m2_binary_le_polytime` in both directions. -/
theorem PvsNP.Units.tl_lang_sum_two_cubes_np :
    ({x : List Bool | ∃ a b : ℕ, a ^ 3 + b ^ 3 = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.NP := by
  refine ⟨PvsNP.Units.tl_lang_sum_two_cubes_np.verifier,
    Polynomial.C 3 * Polynomial.X + Polynomial.C 1,
    PvsNP.Units.tl_lang_sum_two_cubes_np.cpt_verifier, fun x => ?_⟩
  constructor
  · rintro ⟨a, b, hab⟩
    have hxlt : PvsNP.Units.tl_lang_sum_two_cubes_np.val x < 2 ^ x.length :=
      PvsNP.Units.tl_lang_sum_two_cubes_np.val_lt_two_pow x
    have ha_le : a ≤ a ^ 3 := Nat.le_self_pow (by decide) a
    have hb_le : b ≤ b ^ 3 := Nat.le_self_pow (by decide) b
    have halt : a < 2 ^ x.length := by
      change a ^ 3 + b ^ 3 = PvsNP.Units.tl_lang_sum_two_cubes_np.val x at hab
      omega
    have hblt : b < 2 ^ x.length := by
      change a ^ 3 + b ^ 3 = PvsNP.Units.tl_lang_sum_two_cubes_np.val x at hab
      omega
    have halen : (Nat.bits a).length ≤ x.length :=
      PvsNP.Units.tl_lang_sum_two_cubes_np.bits_length_le x.length a halt
    have hblen : (Nat.bits b).length ≤ x.length :=
      PvsNP.Units.tl_lang_sum_two_cubes_np.bits_length_le x.length b hblt
    refine ⟨PvsNP.Units.tl_lang_sum_two_cubes_np.encPair (Nat.bits a) (Nat.bits b), ?_, ?_⟩
    · rw [PvsNP.Units.tl_lang_sum_two_cubes_np.encPair_length]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      omega
    · rw [PvsNP.Units.tl_lang_sum_two_cubes_np.verifier_iff,
        PvsNP.Units.tl_lang_sum_two_cubes_np.val_sumCubes,
        PvsNP.Units.tl_lang_sum_two_cubes_np.decPair_encPair,
        PvsNP.Units.tl_lang_sum_two_cubes_np.val_bits,
        PvsNP.Units.tl_lang_sum_two_cubes_np.val_bits]
      exact hab.symm
  · rintro ⟨w, -, hw⟩
    rw [PvsNP.Units.tl_lang_sum_two_cubes_np.verifier_iff,
      PvsNP.Units.tl_lang_sum_two_cubes_np.val_sumCubes] at hw
    exact ⟨PvsNP.Units.tl_lang_sum_two_cubes_np.val (PvsNP.Units.tl_lang_sum_two_cubes_np.decPair w).1,
      PvsNP.Units.tl_lang_sum_two_cubes_np.val (PvsNP.Units.tl_lang_sum_two_cubes_np.decPair w).2,
      hw.symm⟩
