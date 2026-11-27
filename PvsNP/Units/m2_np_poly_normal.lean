import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_verifier_normal
import PvsNP.Units.fr_ladner

/-- NP with certificate bounds of the form `n ^ k + k` (TM2). Forward: normalize the verifier
so it accepts nothing past its polynomial bound (`m2_np_verifier_normal`), then take `k` with
`p.eval n ≤ n ^ k + k` (`polynomial_le_pow_add`); the larger bound admits no new certificate.
Backward: the bound `n ^ k + k` is the polynomial `X ^ k + C k`. -/
theorem PvsNP.Units.m2_np_poly_normal :
    ∀ L : Language Bool, L ∈ PvsNP.NP ↔
      ∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ x.length ^ k + k ∧ V (x, w) = true := by
  intro L
  constructor
  · intro hL
    obtain ⟨V, p, hV, hbound⟩ := PvsNP.Units.m2_np_verifier_normal L hL
    obtain ⟨hVpoly, hViff⟩ := hV
    obtain ⟨k, hk⟩ := PvsNP.Units.fr_ladner.PEqualNP.Library.Helpers.polynomial_le_pow_add p
    refine ⟨V, k, hVpoly, ?_⟩
    intro x
    constructor
    · intro hx
      obtain ⟨w, hw, hVw⟩ := (hViff x).mp hx
      exact ⟨w, le_trans hw (hk x.length), hVw⟩
    · rintro ⟨w, hw, hVw⟩
      exact (hViff x).mpr ⟨w, hbound x w hVw, hVw⟩
  · rintro ⟨V, k, hVpoly, hV⟩
    show ∃ (V : List Bool × List Bool → Bool) (p : Polynomial ℕ), PvsNP.PolyTimeVerifier L V p
    refine ⟨V, Polynomial.X ^ k + Polynomial.C k, hVpoly, ?_⟩
    intro x
    have heval : (Polynomial.X ^ k + Polynomial.C k).eval x.length = x.length ^ k + k := by
      simp
    rw [heval]
    exact hV x
