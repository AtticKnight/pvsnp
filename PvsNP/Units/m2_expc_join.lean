import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_join
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_karp_trans

set_option autoImplicit false

/-- The join of an exponential-time-complete language with an exponential-time
language is exponential-time-complete (TM2).

Part 1 (the join is in EXP) is exactly the settled unit `m2_exp_join` applied
to the two EXP hypotheses. Part 2 (every EXP language Karp-reduces to the
join) composes the completeness hypothesis (`L'` reduces to `L₁`) with the
settled unit `m2_join_karp_sides` (`L₁` reduces to the join) via the settled
transitivity unit `m2_karp_trans`. -/
theorem PvsNP.Units.m2_expc_join :
    ∀ L₁ L₂ : Language Bool, (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  (∀ L' : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      PvsNP.KarpReducible L' L₁) →
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧
    (∀ L' : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
        PvsNP.KarpReducible L' ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool)) := by
  intro L₁ L₂ h1 hcomp h2
  refine ⟨?_, ?_⟩
  · exact PvsNP.Units.m2_exp_join L₁ L₂ h1 h2
  · intro L' hL'
    exact PvsNP.Units.m2_karp_trans L' L₁ _
      (hcomp L' hL') (PvsNP.Units.m2_join_karp_sides L₁ L₂).1
