import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_down_closed

/-- An exponential-time-complete language is in NP exactly when all of exponential time is.
Forward: each exponential-time `L'` reduces to `L ∈ NP` (`m2_np_down_closed`). Backward:
apply the right side to `L` itself. -/
theorem PvsNP.Units.m2_expc_in_np_iff :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      (∀ L' : Language Bool,
        (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
              (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
          PvsNP.KarpReducible L' L) →
      (L ∈ PvsNP.NP ↔ ∀ L' : Language Bool,
        (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
              (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) → L' ∈ PvsNP.NP) := by
  intro L hExpL hred
  constructor
  · intro hLNP L' hExpL'
    exact PvsNP.Units.m2_np_down_closed L' L (hred L' hExpL') hLNP
  · intro hAll
    exact hAll L hExpL
