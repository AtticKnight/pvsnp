import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tf_fun_prepend_all
import PvsNP.Units.tl_lang_val_pow_p
import PvsNP.Units.m2_p_down_closed

namespace PvsNP.Units.tl_lang_val_tri_p

/-- Eight times a triangular number, plus one, is an odd square. -/
private theorem triangle_iff_square (v : ℕ) :
    (∃ k : ℕ, 2 * v = k * (k + 1)) ↔ ∃ a : ℕ, 1 + 8 * v = a ^ 2 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨2 * k + 1, by nlinarith [hk]⟩
  · rintro ⟨a, ha⟩
    let t := a / 2
    have parity : a = 2 * t ∨ a = 2 * t + 1 := by
      dsimp [t]
      omega
    rcases parity with he | ho
    · rw [he] at ha
      ring_nf at ha
      omega
    · refine ⟨t, ?_⟩
      rw [ho] at ha
      nlinarith [ha]

end PvsNP.Units.tl_lang_val_tri_p

theorem PvsNP.Units.tl_lang_val_tri_p :
    ({x : List Bool | ∃ k : ℕ, 2 * Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = k * (k + 1)} : Language Bool) ∈ PvsNP.P := by
  apply m2_p_down_closed _ _ _ tl_lang_val_pow_p
  refine ⟨fun x : List Bool => [true, false, false] ++ x,
    tf_fun_prepend_all [true, false, false], ?_⟩
  intro x
  let v := Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)
  change (∃ k : ℕ, 2 * v = k * (k + 1)) ↔
    ∃ a : ℕ, Nat.ofDigits 2 (([true, false, false] ++ x).map Bool.toNat) = a ^ 2
  have prefix : Nat.ofDigits (2 : ℕ) (([true, false, false] ++ x).map Bool.toNat) = 1 + 8 * v := by
    simp [v, Nat.ofDigits_cons] <;> ring
  rw [prefix]
  exact tl_lang_val_tri_p.triangle_iff_square v
