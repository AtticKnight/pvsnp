import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_refl
import PvsNP.Units.m2_karp_trans

/-- Follow the cycle from the first index to its end, use the wraparound
edge, and then stop at the second index. This also handles a cycle of length zero. -/
theorem PvsNP.Units.m2_karp_cycle_equiv :
    ∀ (L : ℕ → Language Bool) (n : ℕ),
      (∀ i < n, PvsNP.KarpReducible (L i) (L (i + 1))) →
      PvsNP.KarpReducible (L n) (L 0) →
      ∀ i j : ℕ, i ≤ n → j ≤ n → PvsNP.KarpReducible (L i) (L j) := by
  intro L n edge wrap
  have path : ∀ k, k ≤ n → ∀ i, i ≤ k → PvsNP.KarpReducible (L i) (L k) := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      have e : i = 0 := by omega
      subst i
      exact PvsNP.Units.m2_karp_refl _
    | succ k ih =>
      intro hk i hi
      by_cases e : i = k + 1
      · subst i
        exact PvsNP.Units.m2_karp_refl _
      · exact PvsNP.Units.m2_karp_trans _ _ _ (ih (by omega) i (by omega)) (edge k (by omega))
  intro i j hi hj
  exact PvsNP.Units.m2_karp_trans _ _ _ (path n (by omega) i hi)
    (PvsNP.Units.m2_karp_trans _ _ _ wrap (path j hj 0 (Nat.zero_le j)))
