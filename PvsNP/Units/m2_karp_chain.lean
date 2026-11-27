import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_refl
import PvsNP.Units.m2_karp_trans

/-- Compose the prefix reductions in order, starting with the empty chain. -/
theorem PvsNP.Units.m2_karp_chain :
    ∀ (L : ℕ → Language Bool) (n : ℕ),
      (∀ i < n, PvsNP.KarpReducible (L i) (L (i + 1))) →
        PvsNP.KarpReducible (L 0) (L n) := by
  intro L n
  induction n with
  | zero =>
    intro _
    exact PvsNP.Units.m2_karp_refl _
  | succ n ih =>
    intro edge
    exact PvsNP.Units.m2_karp_trans _ _ _
      (ih (fun i hi => edge i (Nat.lt.step hi))) (edge n (Nat.lt_succ_self n))
