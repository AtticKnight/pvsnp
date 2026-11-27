import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_eq_np_nexp_exp
import PvsNP.Units.m2_exp_compl
import PvsNP.Units.m2_exp_subset_nexp

/-
Unit `m2_p_eq_np_nexp_compl`: if P = NP, then NEXP is closed under complement.

Three settled units chained, exactly as the unit's hint lays out: under P = NP a
language with an exponential-certificate verifier is in exponential time
(`m2_p_eq_np_nexp_exp`); exponential time is closed under complement (`m2_exp_compl`,
negate the decider's answer bit); and an exponential-time language has an
exponential-certificate verifier (`m2_exp_subset_nexp`).
-/

theorem PvsNP.Units.m2_p_eq_np_nexp_compl :
    PvsNP.P = PvsNP.NP → ∀ L : Language Bool,
      (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L ↔
            ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
      (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ Lᶜ ↔
            ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) := by
  intro hEq L hL
  exact PvsNP.Units.m2_exp_subset_nexp Lᶜ
    (PvsNP.Units.m2_exp_compl L (PvsNP.Units.m2_p_eq_np_nexp_exp hEq L hL))
