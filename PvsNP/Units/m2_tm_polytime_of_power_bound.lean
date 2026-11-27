import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_polytime_iff_time_poly

theorem PvsNP.Units.m2_tm_polytime_of_power_bound :
    ∀ {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) (c k : ℕ),
      (∃ M : Turing.TM2ComputableInTime ea eb f, ∀ n : ℕ, M.time n ≤ c * n ^ k + c) →
        PvsNP.PolyTimeComputable ea eb f := by
  intro α β αΓ βΓ ea eb f c k h
  obtain ⟨M, hM⟩ := h
  apply (PvsNP.Units.m2_polytime_iff_time_poly ea eb f).mpr
  refine ⟨Polynomial.C c * Polynomial.X ^ k + Polynomial.C c, M, fun n => ?_⟩
  have hpeval : (Polynomial.C c * Polynomial.X ^ k + Polynomial.C c).eval n
      = c * n ^ k + c := by
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
  rw [hpeval]
  exact hM n
