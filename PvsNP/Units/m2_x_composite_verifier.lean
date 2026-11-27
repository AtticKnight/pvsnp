import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tl_lang_composite_np
import PvsNP.Units.m2_tm_binary_lt
import PvsNP.Units.tr_rel_val_dvd
import PvsNP.Units.m2_tm_pair_bool_combine

-- Built from the settled campaign units tl_lang_composite_np, m2_tm_binary_lt, tr_rel_val_dvd (make.fun pvsnp campaign).

set_option autoImplicit false

namespace PvsNP.Units.m2_x_composite_verifier

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem cpt_V :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (1 < Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) ∧
          Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ∧
            Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) ∣ Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat))) := by
  obtain ⟨f, hf, hfs⟩ := PvsNP.Units.tr_rel_val_dvd
  have h1 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => p.2.tail.any id) :=
    cpt_comp (cpt_comp cpt_snd cpt_tail) PvsNP.Units.tl_lang_composite_np.cpt_any_id
  have h2 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool =>
        decide (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat))) :=
    cpt_comp cpt_swap PvsNP.Units.m2_tm_binary_lt
  have h3 : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
      (fun p : List Bool × List Bool => f (p.2, p.1)) :=
    cpt_comp cpt_swap hf
  have hall := PvsNP.Units.m2_tm_pair_bool_combine (· && ·) _ _
    (PvsNP.Units.m2_tm_pair_bool_combine (· && ·) _ _ h1 h2) h3
  have hone : ∀ s : List Bool, s.tail.any id = true ↔ 1 < Nat.ofDigits (2 : ℕ) (s.map Bool.toNat) :=
    fun s => (PvsNP.Units.tl_lang_composite_np.one_lt_val_iff s).symm
  have hd : ∀ p : List Bool × List Bool, f (p.2, p.1) = true ↔
      Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) ∣ Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) :=
    fun p => (hfs (p.2, p.1)).symm
  have key : (fun p : List Bool × List Bool =>
        decide (1 < Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) ∧
          Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ∧
            Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) ∣ Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat))) =
      (fun p : List Bool × List Bool =>
        (p.2.tail.any id &&
          decide (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat))) &&
            f (p.2, p.1)) := by
    funext p
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, hd, hone, and_assoc]
  rw [key]
  exact hall

end PvsNP.Units.m2_x_composite_verifier

theorem PvsNP.Units.m2_x_composite_verifier :
    PvsNP.PolyTimeVerifier ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool)
      (fun p : List Bool × List Bool =>
        decide (1 < Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) ∧
          Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) < Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ∧
            Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat) ∣ Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat)))
      Polynomial.X := by
  have _hc := Classical.em True
  refine ⟨PvsNP.Units.m2_x_composite_verifier.cpt_V, fun x => ?_⟩
  change (∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = PvsNP.Units.tl_lang_composite_np.val x) ↔
    ∃ w : List Bool, w.length ≤ (Polynomial.X : Polynomial ℕ).eval x.length ∧
      decide (1 < PvsNP.Units.tl_lang_composite_np.val w ∧
        PvsNP.Units.tl_lang_composite_np.val w < PvsNP.Units.tl_lang_composite_np.val x ∧
          PvsNP.Units.tl_lang_composite_np.val w ∣ PvsNP.Units.tl_lang_composite_np.val x) = true
  simp only [Polynomial.eval_X, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have hlt := PvsNP.Units.tl_lang_composite_np.val_lt_two_pow x
    have hab' : a < a * b := by nlinarith
    have hax : a < PvsNP.Units.tl_lang_composite_np.val x := by rw [← hab]; exact hab'
    refine ⟨Nat.bits a, ?_, ?_⟩
    · exact PvsNP.Units.tl_lang_composite_np.bits_length_le_of_lt_two_pow (lt_trans hax hlt)
    · rw [PvsNP.Units.tl_lang_composite_np.val_bits]
      exact ⟨ha, hax, ⟨b, hab.symm⟩⟩
  · rintro ⟨w, _, h1, h2, k, hk⟩
    refine ⟨PvsNP.Units.tl_lang_composite_np.val w, k, h1, ?_, hk.symm⟩
    by_contra hk1
    have hk1' : k ≤ 1 := not_lt.1 hk1
    have hle : PvsNP.Units.tl_lang_composite_np.val w * k ≤ PvsNP.Units.tl_lang_composite_np.val w * 1 :=
      Nat.mul_le_mul_left _ hk1'
    rw [mul_one] at hle
    rw [hk] at h2
    exact absurd h2 (not_lt.2 hle)
