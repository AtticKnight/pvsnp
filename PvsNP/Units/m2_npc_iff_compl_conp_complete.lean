import Mathlib
import PvsNP.Defs
import CookLevin

/-
Unit `m2_npc_iff_compl_conp_complete`: `L` is NP-complete exactly when its complement
is coNP-complete.

No machine work is needed: everything is definition unfolding plus the fact that one
function `f` reduces `L'ᶜ` to `L` exactly when it reduces `L'` to `Lᶜ` (a reduction
preserves and reflects membership, so it does the same for the complements).
Concretely, `Lᶜ ∈ coNP` unfolds to `Lᶜᶜ = L ∈ NP`, and `∀ L' ∈ coNP, KarpReducible L' Lᶜ`
is the same condition as `∀ M ∈ NP, KarpReducible M L` after substituting `M = L'ᶜ`
(every language is the complement of its complement).
-/

namespace PvsNP.Units.m2_npc_iff_compl_conp_complete

/-- A reduction `L'ᶜ ≤ L` is the same function as a reduction `L' ≤ Lᶜ`. -/
theorem karp_compl_left {L' L : Language Bool} :
    PvsNP.KarpReducible L'ᶜ L ↔ PvsNP.KarpReducible L' Lᶜ := by
  constructor
  · -- hiff : x ∈ L'ᶜ ↔ f x ∈ L; goal: x ∈ L' ↔ f x ∈ Lᶜ
    rintro ⟨f, hf, hiff⟩
    refine ⟨f, hf, fun x => ?_⟩
    constructor
    · intro hx hfx
      exact (hiff x).mpr hfx hx
    · intro hfx
      by_contra hx
      exact hfx ((hiff x).mp hx)
  · -- hiff : x ∈ L' ↔ f x ∈ Lᶜ; goal: x ∈ L'ᶜ ↔ f x ∈ L
    rintro ⟨f, hf, hiff⟩
    refine ⟨f, hf, fun x => ?_⟩
    constructor
    · intro hx
      by_contra hfx
      exact hx ((hiff x).mpr hfx)
    · intro hfx hx
      exact (hiff x).mp hx hfx

end PvsNP.Units.m2_npc_iff_compl_conp_complete

theorem PvsNP.Units.m2_npc_iff_compl_conp_complete :
    ∀ L : Language Bool, PvsNP.NPComplete L ↔
      (Lᶜ ∈ PvsNP.coNP ∧ ∀ L' ∈ PvsNP.coNP, PvsNP.KarpReducible L' Lᶜ) := by
  intro L
  constructor
  · rintro ⟨hNP, hhard⟩
    refine ⟨?_, ?_⟩
    · show Lᶜᶜ ∈ PvsNP.NP
      rw [compl_compl]
      exact hNP
    · intro L' hL'
      have hred := hhard L'ᶜ hL'
      exact (PvsNP.Units.m2_npc_iff_compl_conp_complete.karp_compl_left).mp hred
  · rintro ⟨hcompl, hhard'⟩
    refine ⟨?_, ?_⟩
    · have h : Lᶜᶜ ∈ PvsNP.NP := hcompl
      rwa [compl_compl] at h
    · intro M hM
      have hM' : Mᶜ ∈ PvsNP.coNP := by
        show Mᶜᶜ ∈ PvsNP.NP
        rw [compl_compl]
        exact hM
      have hred := hhard' Mᶜ hM'
      have hred2 := (PvsNP.Units.m2_npc_iff_compl_conp_complete.karp_compl_left
        (L' := M) (L := Lᶜ)).mp hred
      rwa [compl_compl] at hred2
