import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_binary_le_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_tm_pair_ite_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.tf_fun_succ

set_option autoImplicit false

namespace PvsNP.Units.tf_fun_pair_min

/-- The smaller of the two numerals, as a normalized binary string. -/
theorem main :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (min (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat))
          (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))) := by
  -- the two projections are polytime
  obtain ⟨h1, h2, -⟩ := PvsNP.Units.m2_pair_split_polytime
  -- compare the two numerals (decide ≤) in polytime
  have hcmp := PvsNP.Units.m2_binary_le_polytime
  -- select the smaller numeral as a list
  have hsel := PvsNP.Units.m2_tm_pair_ite_polytime
    (fun p : List Bool × List Bool =>
      decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤
        Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))
    (fun p : List Bool × List Bool => p.1) (fun p : List Bool × List Bool => p.2)
    hcmp h1 h2
  -- normalize it (strip trailing falses): T is polytime via the succ unit's pieces
  have hrev := PvsNP.Units.m2_reverse_polytime
  have hdw := PvsNP.Units.tf_fun_succ.dw_poly
  -- dw ∘ reverse
  have hA := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => x.reverse)
    (PvsNP.Units.tf_fun_succ.dw false) hrev hdw
  -- T = reverse ∘ (dw ∘ reverse)
  have hT2 := PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString
    PvsNP.encodeString
    (fun x : List Bool => (x.reverse.dropWhile (fun b => !b)))
    (fun x : List Bool => x.reverse) hA hrev
  -- the normalizer equals T
  have hTeq : ((fun x : List Bool => x.reverse) ∘
      fun x : List Bool => (x.reverse.dropWhile (fun b => !b))) =
      PvsNP.Units.tf_fun_succ.T := by
    funext x
    exact (PvsNP.Units.tf_fun_succ.T_eq x).symm
  rw [hTeq] at hT2

  -- compose selection with normalization
  have hcomp := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString
    PvsNP.encodeString
    (fun p : List Bool × List Bool =>
      if decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤
          Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)) then p.1 else p.2)
    PvsNP.Units.tf_fun_succ.T hsel hT2
  -- the composed function is exactly the target
  have hfun : (PvsNP.Units.tf_fun_succ.T ∘
          (fun p : List Bool × List Bool =>
            if decide (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤
                Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)) then p.1 else p.2)) =
      (fun p : List Bool × List Bool =>
        Nat.bits (min (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat))
          (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))) := by
    funext p
    simp only [Function.comp_apply, PvsNP.Units.tf_fun_succ.T_eq]
    rcases le_total (Nat.ofDigits 2 (p.1.map Bool.toNat))
        (Nat.ofDigits 2 (p.2.map Bool.toNat)) with h | h
    · simp only [decide_eq_true h, min_eq_left h]
      exact (PvsNP.Units.tf_fun_succ.bits_val p.1).symm
    · by_cases hab : Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat) ≤
        Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)
      · simp only [decide_eq_true hab, min_eq_left hab]
        exact (PvsNP.Units.tf_fun_succ.bits_val p.1).symm
      · simp only [decide_eq_false hab, min_eq_right h]
        exact (PvsNP.Units.tf_fun_succ.bits_val p.2).symm
  rw [← hfun]
  exact hcomp

end PvsNP.Units.tf_fun_pair_min

theorem PvsNP.Units.tf_fun_pair_min :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool =>
        Nat.bits (min (Nat.ofDigits (2 : ℕ) (p.1.map Bool.toNat))
          (Nat.ofDigits (2 : ℕ) (p.2.map Bool.toNat)))) :=
  PvsNP.Units.tf_fun_pair_min.main
