import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_compl
import PvsNP.Units.m2_exp_subset_nexp

namespace PvsNP.Units.m2_nexp_in_exp_compl

theorem nexp_in_exp_compl_main :
(∀ L : Language Bool, (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) → (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)) →
  ∀ L : Language Bool, (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
      ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) → (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
      ∀ x : List Bool, x ∈ Lᶜ ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true)
  := by
  intro h L hL
  exact PvsNP.Units.m2_exp_subset_nexp Lᶜ (PvsNP.Units.m2_exp_compl L (h L hL))

end PvsNP.Units.m2_nexp_in_exp_compl

theorem PvsNP.Units.m2_nexp_in_exp_compl :
(∀ L : Language Bool, (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) → (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)) →
  ∀ L : Language Bool, (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
      ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) → (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
      ∀ x : List Bool, x ∈ Lᶜ ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true)
  :=
  PvsNP.Units.m2_nexp_in_exp_compl.nexp_in_exp_compl_main
