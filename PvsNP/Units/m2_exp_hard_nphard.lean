import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_np_in_exp
import PvsNP.Units.m2_exp_poly_exponent

set_option autoImplicit false

/-- If every exponential-time language reduces to L, then L is NP-hard, since NP is contained in EXP. -/
theorem PvsNP.Units.m2_exp_hard_nphard :
    ∀ L : Language Bool,
      (∀ L' : Language Bool,
        (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
              (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
          PvsNP.KarpReducible L' L) →
      PvsNP.NPHard L := by
  intro L hHard L' hNP
  obtain ⟨f, hf, M, k, htime⟩ := PvsNP.Units.fr_np_in_exp L' hNP
  have hpoly : ∃ (p : Polynomial ℕ) (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ p.eval n := by
    refine ⟨Polynomial.X ^ k + Polynomial.C k, f, M, hf, fun n => ?_⟩
    have hpow : (Polynomial.X ^ k + Polynomial.C k).eval n = n ^ k + k := by simp
    rw [hpow]
    exact htime n
  exact hHard L' ((PvsNP.Units.m2_exp_poly_exponent L').mpr hpoly)
