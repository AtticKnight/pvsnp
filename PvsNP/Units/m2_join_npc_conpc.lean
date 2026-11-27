import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_karp_trans
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_npc_join

theorem PvsNP.Units.m2_join_npc_conpc :
    ∀ L₁ L₂ : Language Bool, PvsNP.NPComplete L₁ → L₂ ∈ PvsNP.coNP →
      (∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' L₂) →
        PvsNP.NPHard ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ∧
          (∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool)) ∧
            (({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ∈ PvsNP.NP ↔ PvsNP.NP = PvsNP.coNP) := by
  intro L₁ L₂ h₁ h₂ hhard₂
  have hsides := PvsNP.Units.m2_join_karp_sides L₁ L₂
  have hcoJ : ∀ L' ∈ PvsNP.coNP,
      PvsNP.KarpReducible L' ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) :=
    fun L' hL' => PvsNP.Units.m2_karp_trans L' L₂ _ (hhard₂ L' hL') hsides.2
  refine ⟨?_, hcoJ, ?_⟩
  · intro L' hL'
    exact PvsNP.Units.m2_karp_trans L' L₁ _ (h₁.2 L' hL') hsides.1
  · constructor
    · intro hJ
      have hsub : ∀ M : Language Bool, M ∈ PvsNP.coNP → M ∈ PvsNP.NP :=
        fun M hM => PvsNP.Units.m2_np_down_closed M _ (hcoJ M hM) hJ
      ext M
      constructor
      · intro hM
        change Mᶜ ∈ PvsNP.NP
        exact hsub Mᶜ (by change Mᶜᶜ ∈ PvsNP.NP; simpa using hM)
      · exact hsub M
    · intro heq
      have h₂NP : L₂ ∈ PvsNP.NP := by
        rw [heq]
        exact h₂
      exact (PvsNP.Units.m2_npc_join L₁ L₂ h₁ h₂NP).1.1
