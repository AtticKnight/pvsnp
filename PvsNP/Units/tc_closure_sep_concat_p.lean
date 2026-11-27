import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_in_p
import PvsNP.Units.m2_p_concat

set_option autoImplicit false

theorem PvsNP.Units.tc_closure_sep_concat_p :
    ∀ L₁ L₂ : Language Bool, L₁ ∈ PvsNP.P → L₂ ∈ PvsNP.P →
      ({x : List Bool | ∃ u v : List Bool, x = u ++ false :: v ∧ u ∈ L₁ ∧ v ∈ L₂} : Language Bool) ∈ PvsNP.P := by
  intro L₁ L₂ h1 h2
  have h2' : ({y : List Bool | ∃ v ∈ L₂, y = false :: v} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_join_in_p.cons_in_p false h2
  have hcat := PvsNP.Units.m2_p_concat L₁ _ h1 h2'
  have heq : ({x : List Bool | ∃ u w : List Bool, x = u ++ w ∧ u ∈ L₁ ∧
        w ∈ ({y : List Bool | ∃ v ∈ L₂, y = false :: v} : Language Bool)} : Language Bool) =
      ({x : List Bool | ∃ u v : List Bool, x = u ++ false :: v ∧ u ∈ L₁ ∧ v ∈ L₂} : Language Bool) := by
    ext x
    constructor
    · rintro ⟨u, w, rfl, hu, ⟨v, hv, rfl⟩⟩
      exact ⟨u, v, rfl, hu, hv⟩
    · rintro ⟨u, v, rfl, hu, hv⟩
      exact ⟨u, false :: v, rfl, hu, ⟨v, hv, rfl⟩⟩
  rw [← heq]
  exact hcat
