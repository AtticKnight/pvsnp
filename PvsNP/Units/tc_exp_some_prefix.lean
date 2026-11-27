import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tc_exp_concat
import PvsNP.Units.m2_p_subset_exp
import PvsNP.Units.m2_p_trivial

set_option autoImplicit false

theorem PvsNP.Units.tc_exp_some_prefix :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ y : List Bool, y <+: x ∧ y ∈ L) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L hL
  have hUniv := PvsNP.Units.m2_p_subset_exp (Set.univ : Set (List Bool)) PvsNP.Units.m2_p_trivial.2
  obtain ⟨k, f, M, hf, hM⟩ := PvsNP.Units.tc_exp_concat L (Set.univ : Set (List Bool)) hL hUniv
  refine ⟨k, f, M, fun x => ?_, hM⟩
  rw [← hf x]
  constructor
  · rintro ⟨y, ⟨t, rfl⟩, hy⟩; exact ⟨y, t, rfl, hy, trivial⟩
  · rintro ⟨u, v, rfl, hu, _⟩; exact ⟨u, ⟨v, rfl⟩, hu⟩
