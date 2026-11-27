import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_eq_np_conp
import PvsNP.Units.m2_polytime_comp

/-- If P = NP, the second level Σ₂ of the polynomial hierarchy is in P: a coNP predicate
becomes a P predicate (P = NP gives NP = coNP, settled in `m2_p_eq_np_conp`), its decider
composed with the polytime map (`m2_polytime_comp`) is a polytime verifier for the bounded
existential, so the language is NP, hence P. -/
theorem PvsNP.Units.m2_p_eq_np_sigma2 :
    PvsNP.P = PvsNP.NP → ∀ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.coNP → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g →
        ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E} : Language Bool) ∈ PvsNP.P := by
  intro hPNP E g p hE hg
  have hNPcoNP := PvsNP.Units.m2_p_eq_np_conp hPNP
  have hE_NP : E ∈ PvsNP.NP := by rw [hNPcoNP]; exact hE
  have hE_P : E ∈ PvsNP.P := by rw [hPNP]; exact hE_NP
  have hE_P' : PvsNP.PolyTimeDecidable E := hE_P
  obtain ⟨e, he, hdec⟩ := hE_P'
  have hV : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer (fun q => e (g q)) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeAnswer g e hg he
  have hL_NP : ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E} : Language Bool) ∈ PvsNP.NP := by
    refine ⟨fun q => e (g q), p, hV, fun x => ?_⟩
    show (∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E) ↔
      ∃ w : List Bool, w.length ≤ p.eval x.length ∧ e (g (x, w)) = true
    constructor
    · rintro ⟨c, hc, hgc⟩
      exact ⟨c, hc, (hdec (g (x, c))).1 hgc⟩
    · rintro ⟨c, hc, hVc⟩
      exact ⟨c, hc, (hdec (g (x, c))).2 hVc⟩
  rw [hPNP]
  exact hL_NP
