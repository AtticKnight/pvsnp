import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_pair_build_polytime
import PvsNP.Units.m2_eq_polytime
import PvsNP.Units.tf_fun_pair_add
import PvsNP.Units.tf_fun_pair_mul

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_sum_three_squares_np

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

def val (x : List Bool) : ℕ := Nat.ofDigits 2 (x.map Bool.toNat)

theorem val_cons (b : Bool) (xs : List Bool) :
    val (b :: xs) = b.toNat + 2 * val xs := by
  simp [val, Nat.ofDigits]

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

def binAdd (a b : List Bool) : List Bool := Nat.bits (val a + val b)
def binMul (a b : List Bool) : List Bool := Nat.bits (val a * val b)

theorem cpt_binAdd_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => binAdd (f s) (g s)) :=
  cpt_comp (f := fun s => (f s, g s))
    (g := fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) + Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    (PvsNP.Units.m2_pair_build_polytime f g hf hg) PvsNP.Units.tf_fun_pair_add

theorem cpt_binMul_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => binMul (f s) (g s)) :=
  cpt_comp (f := fun s => (f s, g s))
    (g := fun p : List Bool × List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) * Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    (PvsNP.Units.m2_pair_build_polytime f g hf hg) PvsNP.Units.tf_fun_pair_mul

theorem cpt_eq_fun (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f)
    (hg : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString g) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer (fun s => decide (f s = g s)) :=
  cpt_comp (PvsNP.Units.m2_pair_build_polytime f g hf hg) PvsNP.Units.m2_eq_polytime

def sum3 (w : List Bool) : List Bool :=
  binAdd
    (binAdd (binMul (unpairB w).1 (unpairB w).1)
            (binMul (unpairB (unpairB w).2).1 (unpairB (unpairB w).2).1))
    (binMul (unpairB (unpairB w).2).2 (unpairB (unpairB w).2).2)

theorem cpt_sum3 :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString sum3 := by
  have hA : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1_1 cpt_id
  have hBC : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  have hB : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB (unpairB s).2).1) :=
    cpt_unpairB1_1 hBC
  have hC : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB (unpairB s).2).2) :=
    cpt_unpairB2_1 hBC
  have hA2 := cpt_binMul_fun _ _ hA hA
  have hB2 := cpt_binMul_fun _ _ hB hB
  have hC2 := cpt_binMul_fun _ _ hC hC
  exact cpt_binAdd_fun _ _ (cpt_binAdd_fun _ _ hA2 hB2) hC2

theorem cpt_verifier_of (F : List Bool → List Bool)
    (hF : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString F) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (F (unpairB (pairB p.1 p.2)).2 = binAdd (unpairB (pairB p.1 p.2)).1 [])) := by
  have hX : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).1) :=
    cpt_unpairB1_1 cpt_id
  have hW : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => (unpairB s).2) :=
    cpt_unpairB2_1 cpt_id
  have hL : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => F (unpairB s).2) :=
    cpt_comp (f := fun s => (unpairB s).2) (g := F) hW hF
  have hR : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun s => binAdd (unpairB s).1 []) :=
    cpt_binAdd_fun _ _ hX (cpt_const [])
  have hStr := cpt_eq_fun _ _ hL hR
  exact cpt_comp cpt_pairB hStr

theorem sum3_eq (A B C : List Bool) :
    sum3 (pairB A (pairB B C)) = Nat.bits (val A ^ 2 + val B ^ 2 + val C ^ 2) := by
  simp only [sum3, unpairB_pairB, binAdd, binMul, val_bits, sq]

end PvsNP.Units.tl_lang_sum_three_squares_np

/-- The strings whose binary value is a sum of three squares are in NP (TM2). -/
theorem PvsNP.Units.tl_lang_sum_three_squares_np :
    ({x : List Bool | ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.NP := by
  refine ⟨_, Polynomial.C 5 * Polynomial.X + Polynomial.C 2,
    PvsNP.Units.tl_lang_sum_three_squares_np.cpt_verifier_of
      PvsNP.Units.tl_lang_sum_three_squares_np.sum3
      PvsNP.Units.tl_lang_sum_three_squares_np.cpt_sum3, fun x => ?_⟩
  change (∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = PvsNP.Units.tl_lang_sum_three_squares_np.val x) ↔
    ∃ w : List Bool, w.length ≤ (Polynomial.C 5 * Polynomial.X + Polynomial.C 2).eval x.length ∧
      decide (PvsNP.Units.tl_lang_sum_three_squares_np.sum3
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB x w)).2 =
        PvsNP.Units.tl_lang_sum_three_squares_np.binAdd
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
            (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB x w)).1 []) = true
  constructor
  · rintro ⟨a, b, c, habc⟩
    let A := Nat.bits a
    let B := Nat.bits b
    let C := Nat.bits c
    let w := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB A
      (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB B C)
    have hlt := PvsNP.Units.tl_lang_sum_three_squares_np.val_lt_two_pow x
    have ha_le : a ≤ a ^ 2 := by nlinarith
    have hb_le : b ≤ b ^ 2 := by nlinarith
    have hc_le : c ≤ c ^ 2 := by nlinarith
    have hAlen : A.length ≤ x.length :=
      PvsNP.Units.tl_lang_sum_three_squares_np.bits_length_le_of_lt_two_pow (by omega)
    have hBlen : B.length ≤ x.length :=
      PvsNP.Units.tl_lang_sum_three_squares_np.bits_length_le_of_lt_two_pow (by omega)
    have hClen : C.length ≤ x.length :=
      PvsNP.Units.tl_lang_sum_three_squares_np.bits_length_le_of_lt_two_pow (by omega)
    refine ⟨w, ?_, ?_⟩
    · simp only [w, PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB_length,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      omega
    · simp only [w, A, B, C,
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB,
        decide_eq_true_eq, PvsNP.Units.tl_lang_sum_three_squares_np.sum3_eq,
        PvsNP.Units.tl_lang_sum_three_squares_np.binAdd,
        PvsNP.Units.tl_lang_sum_three_squares_np.val_bits]
      simp only [PvsNP.Units.tl_lang_sum_three_squares_np.val, List.map_nil, Nat.ofDigits, Nat.add_zero]
      exact congrArg Nat.bits habc
  · rintro ⟨w, _, hacc⟩
    simp only [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB,
      decide_eq_true_eq, PvsNP.Units.tl_lang_sum_three_squares_np.sum3,
      PvsNP.Units.tl_lang_sum_three_squares_np.binAdd,
      PvsNP.Units.tl_lang_sum_three_squares_np.binMul,
      PvsNP.Units.tl_lang_sum_three_squares_np.val_bits] at hacc
    have h0 : PvsNP.Units.tl_lang_sum_three_squares_np.val [] = 0 := rfl
    rw [h0, Nat.add_zero, PvsNP.Units.tl_lang_sum_three_squares_np.bits_eq_iff] at hacc
    refine ⟨PvsNP.Units.tl_lang_sum_three_squares_np.val (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB w).1,
      PvsNP.Units.tl_lang_sum_three_squares_np.val (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB w).2).1,
      PvsNP.Units.tl_lang_sum_three_squares_np.val (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB w).2).2,
      ?_⟩
    simpa only [sq] using hacc
