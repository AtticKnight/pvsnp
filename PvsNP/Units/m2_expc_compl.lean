import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_compl
import PvsNP.Units.m2_karp_compl_iff

/-
Original proof of `PvsNP.Units.m2_expc_compl`, from the settled units it imports.
-/

theorem PvsNP.Units.m2_expc_compl :
    ∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  (∀ L' : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      PvsNP.KarpReducible L' L) →
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ Lᶜ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧
    ∀ L' : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
        PvsNP.KarpReducible L' Lᶜ := by
  intro L hL hard
  refine ⟨PvsNP.Units.m2_exp_compl L hL, fun L' hL' => ?_⟩
  have h := (PvsNP.Units.m2_karp_compl_iff _ _).mp (hard _ (PvsNP.Units.m2_exp_compl L' hL'))
  rwa [compl_compl] at h
