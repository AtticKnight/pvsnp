import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_concat
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_subset_np

set_option autoImplicit false

/-- NP is closed under marked concatenation (TM2): split a word as `u ++ false :: v`
with `u ∈ L₁` and `v ∈ L₂`. The separator is a singleton language in P, so this
is two plain concatenations: `(L₁ · {[false]}) · L₂`. -/
theorem PvsNP.Units.tc_closure_sep_concat_np : ∀ L₁ L₂ : Language Bool,
    L₁ ∈ PvsNP.NP → L₂ ∈ PvsNP.NP →
    ({x : List Bool | ∃ u v : List Bool, x = u ++ false :: v ∧ u ∈ L₁ ∧ v ∈ L₂} :
      Language Bool) ∈ PvsNP.NP := by
  intro L₁ L₂ hL₁ hL₂
  have hsep : ({x : List Bool | x ∈ ({[false]} : Finset (List Bool))} :
      Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_p_finite _)
  have h1 : ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ∈ L₁ ∧
      v ∈ ({x : List Bool | x ∈ ({[false]} : Finset (List Bool))} : Language Bool)} :
      Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_np_concat L₁ _ hL₁ hsep
  have h2 : ({x : List Bool | ∃ w v : List Bool, x = w ++ v ∧
      w ∈ ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ∈ L₁ ∧
        v ∈ ({x : List Bool | x ∈ ({[false]} : Finset (List Bool))} :
          Language Bool)} : Language Bool) ∧ v ∈ L₂} :
      Language Bool) ∈ PvsNP.NP :=
    PvsNP.Units.m2_np_concat _ L₂ h1 hL₂
  have heq : ({x : List Bool | ∃ w v : List Bool, x = w ++ v ∧
      w ∈ ({x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ∈ L₁ ∧
        v ∈ ({x : List Bool | x ∈ ({[false]} : Finset (List Bool))} :
          Language Bool)} : Language Bool) ∧ v ∈ L₂} :
      Language Bool) =
      ({x : List Bool | ∃ u v : List Bool, x = u ++ false :: v ∧ u ∈ L₁ ∧ v ∈ L₂} :
        Language Bool) := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, v, rfl, ⟨u, s, hws, hu, hs⟩, hv⟩
      have hs' : s = [false] := Finset.mem_singleton.mp hs
      exact ⟨u, v, by simp [hws, hs', List.append_assoc], hu, hv⟩
    · rintro ⟨u, v, rfl, hu, hv⟩
      exact ⟨u ++ [false], v, by simp [List.append_assoc],
        ⟨u, [false], rfl, hu, Finset.mem_singleton_self _⟩, hv⟩
  rw [← heq]
  exact h2
