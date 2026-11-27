import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_conp_join
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_conp_down_closed
import PvsNP.Units.m2_exp_down_closed

namespace PvsNP.Units.m2_join_conp_exp_parts

/-- Each side of the join Karp-reduces to the join. -/
theorem karp_sides (L₁ L₂ : Language Bool) :
    PvsNP.KarpReducible L₁
      ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} :
        Language Bool) ∧
    PvsNP.KarpReducible L₂
      ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} :
        Language Bool) :=
  PvsNP.Units.m2_join_karp_sides L₁ L₂

end PvsNP.Units.m2_join_conp_exp_parts

theorem PvsNP.Units.m2_join_conp_exp_parts :
    ∀ L₁ L₂ : Language Bool,
      (({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} :
          Language Bool) ∈ PvsNP.coNP ↔ L₁ ∈ PvsNP.coNP ∧ L₂ ∈ PvsNP.coNP) ∧
        ((∃ k : ℕ, ∃ (f : List Bool → Bool)
            (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
              (∀ x : List Bool, x ∈ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨
                  (∃ y ∈ L₂, x = true :: y)} : Language Bool) ↔ f x = true) ∧
                ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
          (∃ k : ℕ, ∃ (f : List Bool → Bool)
              (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
                (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧
                  ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧
          (∃ k : ℕ, ∃ (f : List Bool → Bool)
              (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
                (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧
                  ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)) := by
  intro L₁ L₂
  obtain ⟨h₁, h₂⟩ := PvsNP.Units.m2_join_conp_exp_parts.karp_sides L₁ L₂
  refine ⟨⟨fun hJ => ⟨PvsNP.Units.m2_conp_down_closed L₁ _ h₁ hJ,
      PvsNP.Units.m2_conp_down_closed L₂ _ h₂ hJ⟩,
    fun h => PvsNP.Units.m2_conp_join L₁ L₂ h.1 h.2⟩, fun hExp =>
    ⟨PvsNP.Units.m2_exp_down_closed L₁ _ h₁ hExp,
      PvsNP.Units.m2_exp_down_closed L₂ _ h₂ hExp⟩⟩
