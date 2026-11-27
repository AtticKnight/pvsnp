import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_eq_np_sigma2

theorem PvsNP.Units.m2_p_eq_np_pi2 :
    PvsNP.P = PvsNP.NP → ∀ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.NP → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g →
        ({x : List Bool | ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E} : Language Bool) ∈ PvsNP.P := by
  intro hPNP E g p hE hg
  have hEc_coNP : Eᶜ ∈ PvsNP.coNP := by
    show Eᶜᶜ ∈ PvsNP.NP
    simpa using hE
  have hS := PvsNP.Units.m2_p_eq_np_sigma2 hPNP Eᶜ g p hEc_coNP hg
  have hSc := PvsNP.Units.m2_p_compl _ hS
  have heq : ({x : List Bool | ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E} : Language Bool) =
      ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ Eᶜ} : Language Bool)ᶜ := by
    ext x
    change (∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E) ↔
      ¬ (∃ c : List Bool, c.length ≤ p.eval x.length ∧ ¬ (g (x, c) ∈ E))
    push_neg
    rfl
  rw [heq]
  exact hSc
