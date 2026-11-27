import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.tc_exp_concat
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_subset_exp

/-- Two exponential concatenations allow arbitrary material on either side of a factor. -/
theorem PvsNP.Units.tc_exp_some_factor :
    ∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, (∃ y : List Bool, y <:+: x ∧ y ∈ L) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L hL
  have topExp := PvsNP.Units.m2_p_subset_exp (Set.univ : Language Bool) PvsNP.Units.m2_p_trivial.2
  let withTail : Language Bool := {z | ∃ a b : List Bool,
    z = a ++ b ∧ a ∈ L ∧ b ∈ (Set.univ : Language Bool)}
  have tailExp := PvsNP.Units.tc_exp_concat L Set.univ hL topExp
  obtain ⟨k, f, M, spec, bound⟩ := PvsNP.Units.tc_exp_concat Set.univ withTail topExp tailExp
  refine ⟨k, f, M, ?_, bound⟩
  intro x
  refine Iff.trans ?_ (spec x)
  constructor
  · rintro ⟨w, ⟨left, right, rfl⟩, hw⟩
    exact ⟨left, w ++ right, by simp [List.append_assoc], trivial,
      w, right, rfl, hw, trivial⟩
  · rintro ⟨left, tail, rfl, _, w, right, rfl, hw, _⟩
    exact ⟨w, ⟨left, right, by simp [List.append_assoc]⟩, hw⟩
