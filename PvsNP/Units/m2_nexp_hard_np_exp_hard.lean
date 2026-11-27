import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_subset_nexp
import PvsNP.Units.m2_np_subset_nexp

/-- A language every NEXP language reduces to is NP-hard and exponential-time-hard (TM2). -/
theorem PvsNP.Units.m2_nexp_hard_np_exp_hard :
    ∀ L : Language Bool,
      (∀ L' : Language Bool,
        (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
          PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
            ∀ x : List Bool, x ∈ L' ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
          PvsNP.KarpReducible L' L) →
      PvsNP.NPHard L ∧
        ∀ L' : Language Bool,
          (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
                (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
            PvsNP.KarpReducible L' L := by
  intro L H
  constructor
  · intro L' hL'
    exact H L' (PvsNP.Units.m2_np_subset_nexp L' hL')
  · intro L' hL'
    exact H L' (PvsNP.Units.m2_exp_subset_nexp L' hL')
