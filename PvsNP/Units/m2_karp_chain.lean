import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_refl
import PvsNP.Units.m2_karp_trans

/-- A chain of Karp reductions `L₀ ≤ L₁ ≤ … ≤ Lₙ` gives `L₀ ≤ Lₙ` (TM2). -/
theorem PvsNP.Units.m2_karp_chain :
    ∀ (L : ℕ → Language Bool) (n : ℕ), (∀ i < n, PvsNP.KarpReducible (L i) (L (i + 1))) →
      PvsNP.KarpReducible (L 0) (L n) := by
  intro L n h
  induction n with
  | zero => exact PvsNP.Units.m2_karp_refl (L 0)
  | succ k ih =>
    exact PvsNP.Units.m2_karp_trans (L 0) (L k) (L (k + 1))
      (ih (fun i hi => h i (Nat.lt_succ_of_lt hi)))
      (h k (Nat.lt_succ_self k))
