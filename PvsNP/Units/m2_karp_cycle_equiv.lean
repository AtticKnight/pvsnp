import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_refl
import PvsNP.Units.m2_karp_trans

set_option autoImplicit false

namespace PvsNP.Units.m2_karp_cycle_equiv

end PvsNP.Units.m2_karp_cycle_equiv

theorem PvsNP.Units.m2_karp_cycle_equiv :
    ∀ (L : ℕ → Language Bool) (n : ℕ), (∀ i < n, PvsNP.KarpReducible (L i) (L (i + 1))) →
      PvsNP.KarpReducible (L n) (L 0) → ∀ i j : ℕ, i ≤ n → j ≤ n → PvsNP.KarpReducible (L i) (L j) := by
  intro L n hstep hcycle i j hi hj
  have chain : ∀ k i, i + k ≤ n → PvsNP.KarpReducible (L i) (L (i + k)) := by
    intro k
    induction k with
    | zero =>
      intro i _
      exact PvsNP.Units.m2_karp_refl (L i)
    | succ k ih =>
      intro i hik
      have h1 := ih i (by omega)
      have h2 := hstep (i + k) (by omega)
      exact PvsNP.Units.m2_karp_trans _ _ _ h1 h2
  by_cases hij : i ≤ j
  · have e : j = i + (j - i) := by omega
    rw [e]
    exact chain (j - i) i (by omega)
  · have h1 : PvsNP.KarpReducible (L i) (L n) := by
      have e : n = i + (n - i) := by omega
      rw [e]
      exact chain (n - i) i (by omega)
    have h2 : PvsNP.KarpReducible (L 0) (L j) := by
      have e : j = 0 + j := by omega
      rw [e]
      exact chain j 0 (by omega)
    exact PvsNP.Units.m2_karp_trans _ _ _
      (PvsNP.Units.m2_karp_trans _ _ _ h1 hcycle) h2
