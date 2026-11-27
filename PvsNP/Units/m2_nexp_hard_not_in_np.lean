import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_nexp_not_in_np
import PvsNP.Units.m2_np_down_closed

set_option autoImplicit false

theorem PvsNP.Units.m2_nexp_hard_not_in_np :
    ∀ L : Language Bool,
      (∀ L' : Language Bool,
        (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
            PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
              ∀ x : List Bool, x ∈ L' ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
          PvsNP.KarpReducible L' L) →
      L ∉ PvsNP.NP := by
  intro L hhard hL
  obtain ⟨L', hL'_nexp, hL'_not_np⟩ := PvsNP.Units.m2_nexp_not_in_np
  exact hL'_not_np (PvsNP.Units.m2_np_down_closed L' L (hhard L' hL'_nexp) hL)
