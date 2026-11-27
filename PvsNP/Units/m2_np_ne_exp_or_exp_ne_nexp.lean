import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_nexp_not_in_np

/-
Some exponential-time language is outside NP, or some NEXP language is outside exponential time.

The settled unit `PvsNP.Units.m2_nexp_not_in_np` gives a NEXP language `L` outside NP. Either `L`
is decided in exponential time, and it is the witness of the first alternative, or it is not, and
it is the witness of the second.
-/

theorem PvsNP.Units.m2_np_ne_exp_or_exp_ne_nexp :
    (∃ L : Language Bool,
        (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧ L ∉ PvsNP.NP) ∨
      ∃ L : Language Bool,
        (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
          PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
            ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) ∧
        ¬ ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  obtain ⟨L, hNEXP, hNP⟩ := PvsNP.Units.m2_nexp_not_in_np
  by_cases h : ∃ k : ℕ, ∃ (f : List Bool → Bool)
      (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k
  · exact Or.inl ⟨L, h, hNP⟩
  · exact Or.inr ⟨L, hNEXP, h⟩
