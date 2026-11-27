import Mathlib
import PvsNP.Defs
import CookLevin

/-- Polynomially bounded means bounded everywhere by c · n^k + c: the forward
    direction absorbs the finitely many small inputs into the constant via
    maxPrefix; the backward direction takes degree k+1 and constant 2c, using
    c ≤ c * n^k and n^k ≤ n^(k+1) for n ≥ 1. -/
theorem PvsNP.Units.m3_inopoly_iff_bound :
    ∀ f : ℕ → ℕ, inOPoly f ↔ ∃ c k : ℕ, ∀ n, f n ≤ c * n ^ k + c := by
  intro f
  constructor
  · rintro ⟨k, c, n0, h⟩
    refine ⟨max c (maxPrefix f n0), k, ?_⟩
    intro n
    by_cases hn : n0 ≤ n
    · calc f n ≤ c * n ^ k := h n hn
        _ ≤ max c (maxPrefix f n0) * n ^ k :=
            Nat.mul_le_mul (Nat.le_max_left _ _) (Nat.le_refl _)
        _ ≤ max c (maxPrefix f n0) * n ^ k + max c (maxPrefix f n0) :=
            Nat.le_add_right _ _
    · have hlt : n < n0 := Nat.lt_of_not_ge hn
      have hle : f n ≤ maxPrefix f n0 := le_maxPrefix f (Nat.le_of_lt hlt)
      calc f n ≤ maxPrefix f n0 := hle
        _ ≤ max c (maxPrefix f n0) := Nat.le_max_right _ _
        _ ≤ max c (maxPrefix f n0) * n ^ k + max c (maxPrefix f n0) := by
            have hz : 0 ≤ max c (maxPrefix f n0) * n ^ k := Nat.zero_le _
            omega
  · rintro ⟨c, k, h⟩
    refine ⟨k + 1, 2 * c, 1, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := hn
    have hpos : 0 < n := hn1
    have hpow1 : 1 ≤ n ^ k := Nat.one_le_pow k n hpos
    have hc : c ≤ c * n ^ k := by
      calc c = c * 1 := (Nat.mul_one c).symm
        _ ≤ c * n ^ k := Nat.mul_le_mul (Nat.le_refl _) hpow1
    have hpow : n ^ k ≤ n ^ (k + 1) := by
      rw [pow_succ]
      calc n ^ k = n ^ k * 1 := (Nat.mul_one _).symm
        _ ≤ n ^ k * n := Nat.mul_le_mul (Nat.le_refl _) hn1
    calc f n ≤ c * n ^ k + c := h n
      _ ≤ c * n ^ k + c * n ^ k := Nat.add_le_add_left hc _
      _ = 2 * c * n ^ k := by ring
      _ ≤ 2 * c * n ^ (k + 1) := Nat.mul_le_mul (Nat.le_refl _) hpow
