import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_down_closed

/-- Completeness reduces each nondeterministic language to the fixed target. Apply downward closure of exponential time. -/
theorem PvsNP.Units.m2_nexpc_in_exp_iff :
    ∀ L : Language Bool,
  (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
      ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
  (∀ L' : Language Bool,
    (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ L' ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
      PvsNP.KarpReducible L' L) →
  ((∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ↔
    ∀ L' : Language Bool,
      (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L' ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
        (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
              (∀ x : List Bool, x ∈ L' ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k)) := by
  intro L hL complete
  constructor
  · intro h L' h'
    exact PvsNP.Units.m2_exp_down_closed L' L (complete L' h') h
  · intro h
    exact h L hL
