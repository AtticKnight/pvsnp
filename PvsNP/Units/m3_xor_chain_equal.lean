import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

open CookLevin

namespace PvsNP.Units.m3_xor_chain_equal

/-- The parity equation for the pair `{i, i + 1}` says exactly that `i` and
    `i + 1` agree on membership in `a`: case on both memberships and
    compute the filter of the two-entry list. -/
theorem pair_iff (a : assgn) (i : ℕ) :
    decide (([i, i + 1].filter (fun v => decide (v ∈ a))).length % 2 = 1) = false ↔
      (i ∈ a ↔ i + 1 ∈ a) := by
  by_cases h1 : i ∈ a <;> by_cases h2 : i + 1 ∈ a <;> simp [h1, h2]

/-- Parity equations `x_i ⊕ x_(i+1) = 0` along a path force all its
    variables equal. -/
theorem chain_aux :
    ∀ (n : ℕ) (a : assgn),
      (∀ i < n, decide (([i, i + 1].filter (fun v => decide (v ∈ a))).length % 2 = 1) = false) ↔
        ∀ i ≤ n, (i ∈ a ↔ 0 ∈ a) := by
  intro n a
  constructor
  · intro h
    have h' : ∀ i < n, (i ∈ a ↔ i + 1 ∈ a) := fun i hi => (pair_iff a i).1 (h i hi)
    have step : ∀ i, i ≤ n → (i ∈ a ↔ 0 ∈ a) := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        exact (h' k (by omega)).symm.trans (ih (by omega))
    exact step
  · intro h i hi
    apply (pair_iff a i).2
    have e1 := h i (by omega)
    have e2 := h (i + 1) (by omega)
    exact e1.trans e2.symm

end PvsNP.Units.m3_xor_chain_equal

/-- Parity equations `x_i ⊕ x_(i+1) = 0` along a path force all its variables
    equal (vendored model). -/
theorem PvsNP.Units.m3_xor_chain_equal :
    ∀ (n : ℕ) (a : assgn),
      (∀ i < n, decide (([i, i + 1].filter (fun v => decide (v ∈ a))).length % 2 = 1) = false) ↔
        ∀ i ≤ n, (i ∈ a ↔ 0 ∈ a) :=
  PvsNP.Units.m3_xor_chain_equal.chain_aux
