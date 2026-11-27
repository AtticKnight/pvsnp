import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_monotone
import PvsNP.Units.m2_karp_compl_iff

/-- A reduction between two languages lifts to their joins with their complements:
the join of `L₁` with `L₁ᶜ` reduces to the join of `L₂` with `L₂ᶜ`, via the
join-monotonicity lemma applied to the given reduction and its complement. -/
theorem PvsNP.Units.m2_karp_join_compl_lift :
    ∀ L₁ L₂ : Language Bool, PvsNP.KarpReducible L₁ L₂ →
      PvsNP.KarpReducible
        ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₁ᶜ, x = true :: y)} : Language Bool)
        ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₂ᶜ, x = true :: y)} : Language Bool) := by
  intro L₁ L₂ h
  exact PvsNP.Units.m2_join_monotone L₁ L₂ L₁ᶜ L₂ᶜ h
    ((PvsNP.Units.m2_karp_compl_iff L₁ L₂).mp h)
