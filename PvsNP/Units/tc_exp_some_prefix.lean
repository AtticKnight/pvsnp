import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tc_exp_concat
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_subset_exp

/-- An accepted prefix leaves an unrestricted suffix. Both languages have exponential deciders. -/
theorem PvsNP.Units.tc_exp_some_prefix :
    ∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ y : List Bool, y <+: x ∧ y ∈ L) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L hL
  have topExp := PvsNP.Units.m2_p_subset_exp (Set.univ : Language Bool) PvsNP.Units.m2_p_trivial.2
  obtain ⟨k, f, M, spec, bound⟩ := PvsNP.Units.tc_exp_concat L Set.univ hL topExp
  refine ⟨k, f, M, ?_, bound⟩
  intro x
  refine Iff.trans ?_ (spec x)
  constructor
  · rintro ⟨w, ⟨tail, rfl⟩, hw⟩
    exact ⟨w, tail, rfl, hw, Set.mem_univ tail⟩
  · rintro ⟨w, tail, rfl, hw, _⟩
    exact ⟨w, ⟨tail, rfl⟩, hw⟩
