import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_down_closed

/-
Original proof of `PvsNP.Units.m2_exp_iff_reduces_to_expc`, from the settled units it imports.
-/

theorem PvsNP.Units.m2_exp_iff_reduces_to_expc :
    ∀ L₀ : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₀ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  (∀ L' : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      PvsNP.KarpReducible L' L₀) →
  ∀ L : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ↔
      PvsNP.KarpReducible L L₀ := by
  intro L₀ hL₀ hard L
  exact ⟨fun hL => hard L hL, fun h => PvsNP.Units.m2_exp_down_closed L L₀ h hL₀⟩
