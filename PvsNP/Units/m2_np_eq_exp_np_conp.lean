import Mathlib

import PvsNP.Defs

import CookLevin

import PvsNP.Units.m2_np_conp_subset_exp

/-- If every exponential-time language is in NP, then NP = coNP.

Proof idea: the settled unit `m2_np_conp_subset_exp` gives every language in NP or
coNP an exponential-time decider (bound `2 ^ (n ^ k) + k`), so the hypothesis applies
to it.
- `coNP ⊆ NP`: for `L ∈ coNP`, the settled unit hands us an exponential-time decider
  for `L` itself, and the hypothesis puts `L` in NP.
- `NP ⊆ coNP`: for `L ∈ NP`, the complement `Lᶜ` is in coNP (its complement is `L`),
  so the settled unit hands us an exponential-time decider for `Lᶜ`, the hypothesis
  puts `Lᶜ` in NP, and that is exactly `L ∈ coNP` by the definition of `coNP`. -/
theorem PvsNP.Units.m2_np_eq_exp_np_conp :
    (∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
        L ∈ PvsNP.NP) →
    PvsNP.NP = PvsNP.coNP := by
  intro H
  apply Set.Subset.antisymm
  · -- NP ⊆ coNP
    intro L hL
    show Lᶜ ∈ PvsNP.NP
    apply H
    have hLc : Lᶜ ∈ PvsNP.coNP := by
      show (Lᶜ)ᶜ ∈ PvsNP.NP
      rwa [compl_compl]
    exact PvsNP.Units.m2_np_conp_subset_exp Lᶜ (Or.inr hLc)
  · -- coNP ⊆ NP
    intro L hL
    exact H L (PvsNP.Units.m2_np_conp_subset_exp L (Or.inr hL))
