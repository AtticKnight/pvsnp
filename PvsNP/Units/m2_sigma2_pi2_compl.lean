import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m2_sigma2_pi2_compl

theorem m2_sigma2_pi2_compl_aux (L : Language Bool) :
    (∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.coNP ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
        ∀ x : List Bool, x ∈ L ↔ ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E) ↔
    ∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.NP ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
        ∀ x : List Bool, x ∈ Lᶜ ↔ ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E := by
  constructor
  · rintro ⟨E, g, p, hE, hg, hL⟩
    have hEc : Eᶜ ∈ PvsNP.NP := hE
    refine ⟨Eᶜ, g, p, hEc, hg, ?_⟩
    intro x
    constructor
    · intro hx c hc
      intro hgc
      exact hx ((hL x).mpr ⟨c, hc, hgc⟩)
    · intro h
      intro hxL
      obtain ⟨c, hc, hgc⟩ := (hL x).mp hxL
      exact h c hc hgc
  · rintro ⟨E, g, p, hE, hg, hL⟩
    refine ⟨Eᶜ, g, p, ?_, hg, ?_⟩
    · show (Eᶜ)ᶜ ∈ PvsNP.NP
      rw [compl_compl]
      exact hE
    · intro x
      constructor
      · intro hx
        by_contra hcon
        have hall : ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E := by
          intro c hc
          by_contra hgc
          exact hcon ⟨c, hc, hgc⟩
        exact (hL x).mpr hall hx
      · rintro ⟨c, hc, hgc⟩
        by_contra hx
        exact hgc ((hL x).mp hx c hc)

end PvsNP.Units.m2_sigma2_pi2_compl

theorem PvsNP.Units.m2_sigma2_pi2_compl :
    ∀ L : Language Bool,
      (∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
        E ∈ PvsNP.coNP ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
          ∀ x : List Bool, x ∈ L ↔ ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E) ↔
      ∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
        E ∈ PvsNP.NP ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
          ∀ x : List Bool, x ∈ Lᶜ ↔ ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E := by
  intro L
  exact PvsNP.Units.m2_sigma2_pi2_compl.m2_sigma2_pi2_compl_aux L
