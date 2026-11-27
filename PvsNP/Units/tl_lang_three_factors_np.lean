import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_pair_bool_combine
import PvsNP.Units.m2_tm_pair_ite_polytime
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.tr_rel_val_dvd
import PvsNP.Units.tl_lang_composite_np

namespace PvsNP.Units.tl_lang_three_factors_np

def val (l : List Bool) : ℕ := Nat.ofDigits (2 : ℕ) (l.map Bool.toNat)

theorem vb (n : ℕ) : val (Nat.bits n) = n := by
  unfold val
  have h := Nat.digits_two_eq_bits n
  have e : (Nat.bits n).map Bool.toNat = Nat.digits 2 n := by
    rw [h]
    apply List.map_congr_left
    intro b _
    cases b <;> rfl
  rw [e, Nat.ofDigits_digits]

theorem v_lt : ∀ l : List Bool, val l < 2 ^ l.length
  | [] => by simp [val]
  | b :: l => by
    have ih := v_lt l
    have e : val (b :: l) = b.toNat + 2 * val l := by simp [val, Nat.ofDigits_cons]
    rw [e, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem bits_len {m k : ℕ} (h : m < 2 ^ k) : (Nat.bits m).length ≤ k := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

def g (dv : List Bool × List Bool → Bool) (p : List Bool × List Bool) : List Bool :=
  if (dv (p.2, p.1) && !decide (val p.1 ≤ val p.2)) = true then p.2 else []

theorem g_poly (dv : List Bool × List Bool → Bool)
    (hdv : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer dv) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (g dv) := by
  have hsw := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => (p.2, p.1)) dv PvsNP.Units.m2_tm_pair_swap_polytime hdv
  have hT := PvsNP.Units.m2_tm_pair_bool_combine (fun a b => a && !b)
    (dv ∘ fun p : List Bool × List Bool => (p.2, p.1))
    (fun p : List Bool × List Bool => decide (val p.1 ≤ val p.2)) hsw
    PvsNP.Units.m2_binary_le_polytime
  have hcst := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => p.1) (fun _ : List Bool => ([] : List Bool))
    PvsNP.Units.m2_pair_split_polytime.1 (PvsNP.Units.m2_const_polytime [])
  exact PvsNP.Units.m2_tm_pair_ite_polytime _ _ _ hT PvsNP.Units.m2_pair_split_polytime.2.1 hcst

end PvsNP.Units.tl_lang_three_factors_np

open PvsNP.Units.tl_lang_three_factors_np in
theorem PvsNP.Units.tl_lang_three_factors_np : ({x : List Bool | ∃ a b c : ℕ, 1 < a ∧ 1 < b ∧ 1 < c ∧ a * b * c = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) ∈ PvsNP.NP := by
  obtain ⟨dv, hdv, hdvs⟩ := PvsNP.Units.tr_rel_val_dvd
  have hnp := PvsNP.Units.m2_np_projection _ (g dv) Polynomial.X
    PvsNP.Units.tl_lang_composite_np (g_poly dv hdv)
  have e : ({x : List Bool | ∃ a b c : ℕ, 1 < a ∧ 1 < b ∧ 1 < c ∧
      a * b * c = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) =
      {x : List Bool | ∃ c : List Bool, c.length ≤ (Polynomial.X : Polynomial ℕ).eval x.length ∧
        g dv (x, c) ∈ ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧
          a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool)} := by
    ext x
    constructor
    · rintro ⟨a, b, c, ha, hb, hc, h⟩
      have h' : a * b * c = val x := h
      have hab : 0 < a * b := Nat.mul_pos (by omega) (by omega)
      have hlt : a * b < val x := by nlinarith
      refine ⟨Nat.bits (a * b), ?_, ?_⟩
      · rw [Polynomial.eval_X]
        exact bits_len (lt_trans hlt (v_lt x))
      · have hd : dv (Nat.bits (a * b), x) = true :=
          (hdvs (Nat.bits (a * b), x)).mp ⟨c, by
            show val x = val (Nat.bits (a * b)) * c
            rw [vb]
            exact h'.symm⟩
        have ht : (dv (Nat.bits (a * b), x) && !decide (val x ≤ val (Nat.bits (a * b)))) = true := by
          rw [hd, vb]
          simp
          exact hlt
        show g dv (x, Nat.bits (a * b)) ∈ _
        unfold g
        rw [if_pos ht]
        exact ⟨a, b, ha, hb, (vb (a * b)).symm⟩
    · rintro ⟨u, _, hmem⟩
      unfold g at hmem
      by_cases ht : (dv (u, x) && !decide (val x ≤ val u)) = true
      · rw [if_pos ht] at hmem
        obtain ⟨a, b, ha, hb, hab⟩ := hmem
        have hab' : a * b = val u := hab
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_le] at ht
        obtain ⟨c, hc⟩ := (hdvs (u, x)).mpr ht.1
        have hc' : val x = val u * c := hc
        refine ⟨a, b, c, ha, hb, ?_, ?_⟩
        · by_contra hcn
          have hle : c ≤ 1 := by omega
          have : val x ≤ val u := by
            rw [hc']
            calc val u * c ≤ val u * 1 := Nat.mul_le_mul_left _ hle
              _ = val u := Nat.mul_one _
          omega
        · show a * b * c = val x
          rw [hab', hc']
      · rw [if_neg ht] at hmem
        obtain ⟨a, b, ha, hb, hab⟩ := hmem
        have hab' : a * b = 0 := by simpa using hab
        have hpos : 0 < a * b := Nat.mul_pos (by omega) (by omega)
        omega
  rw [e]
  exact hnp
