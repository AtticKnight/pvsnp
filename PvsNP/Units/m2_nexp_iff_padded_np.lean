import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_nexp_padded_np
import PvsNP.Units.m2_padded_np_nexp

set_option autoImplicit false

/-- `L` is in `NEXP` iff some exponential padding of `L` is in `NP` (TM2). -/
theorem PvsNP.Units.m2_nexp_iff_padded_np :
    ∀ L : Language Bool,
      (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) ↔
      ∃ k : ℕ, ({s : List Bool | ∃ x : List Bool, x ∈ L ∧
          s = List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x} : Language Bool) ∈ PvsNP.NP := by
  intro L
  constructor
  · exact PvsNP.Units.m2_nexp_padded_np L
  · rintro ⟨k, hk⟩
    exact PvsNP.Units.m2_padded_np_nexp L k hk
