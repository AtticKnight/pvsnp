import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_karp_trans

/-
Closes m2_hard_join_any: `L₁` Karp-reduces to both `join L₁ L₂` and `join L₂ L₁`
by `m2_join_karp_sides`, so transitivity (`m2_karp_trans`) transfers both
NP-hardness and EXP-hardness to either join.
-/

set_option autoImplicit false

/-- Joining an NP-hard or exponential-time-hard language with any language,
either way round, keeps it hard (TM2). -/
theorem PvsNP.Units.m2_hard_join_any :
    ∀ L₁ L₂ : Language Bool,
      (PvsNP.NPHard L₁ → PvsNP.NPHard ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ∧ PvsNP.NPHard ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₁, x = true :: y)} : Language Bool)) ∧
        ((∀ L' : Language Bool,
          (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
                (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
            PvsNP.KarpReducible L' L₁) →
          (∀ L' : Language Bool,
            (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
                  (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
              PvsNP.KarpReducible L' ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool)) ∧
            (∀ L' : Language Bool,
              (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
                    (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
                PvsNP.KarpReducible L' ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₁, x = true :: y)} : Language Bool))) := by
  intro L₁ L₂
  have h12 := (PvsNP.Units.m2_join_karp_sides L₁ L₂).1
  have h21 := (PvsNP.Units.m2_join_karp_sides L₂ L₁).2
  exact ⟨fun hNP => ⟨fun L' hL' => PvsNP.Units.m2_karp_trans L' L₁ _ (hNP L' hL') h12,
      fun L' hL' => PvsNP.Units.m2_karp_trans L' L₁ _ (hNP L' hL') h21⟩,
    fun hExp => ⟨fun L' hL' => PvsNP.Units.m2_karp_trans L' L₁ _ (hExp L' hL') h12,
      fun L' hL' => PvsNP.Units.m2_karp_trans L' L₁ _ (hExp L' hL') h21⟩⟩
