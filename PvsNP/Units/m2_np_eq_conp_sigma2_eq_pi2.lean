import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_eq_conp_sigma2

/-
Built on the settled units PvsNP.Units.fr_ladner and PvsNP.Units.m2_np_eq_conp_sigma2
of github.com/makedotfun/pvsnp (Apache License 2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_np_eq_conp_sigma2_eq_pi2

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

private theorem encodePair_eq :
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair = PvsNP.encodePair := rfl

private theorem cptE' {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {f g : α → β} (h : ComputableInPolyTime ea eb f) (heq : ∀ a, f a = g a) :
    ComputableInPolyTime ea eb g := by
  obtain rfl : f = g := funext heq
  exact h

private theorem cpt_fst :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1) := by
  rw [← encodePair_eq]
  refine cptE' (cpt_comp cpt_pairB cpt_unpairB1) ?_
  rintro ⟨a, b⟩
  simp only [Function.comp_apply, unpairB_pairB]

theorem main :
    PvsNP.NP = PvsNP.coNP → ∀ L : Language Bool,
      (∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
        E ∈ PvsNP.coNP ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
          ∀ x : List Bool, x ∈ L ↔ ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E) ↔
      ∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
        E ∈ PvsNP.NP ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
          ∀ x : List Bool, x ∈ L ↔ ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E := by
  intro hEq L
  constructor
  · rintro ⟨E, g, p, hE, hg, hspec⟩
    have hL_eq : L = ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E} : Language Bool) := by
      ext x
      exact hspec x
    have hL_NP : L ∈ PvsNP.NP := by
      rw [hL_eq]
      exact PvsNP.Units.m2_np_eq_conp_sigma2 hEq E g p hE hg
    refine ⟨L, fun pair => pair.1, 0, hL_NP, cpt_fst, fun x => ?_⟩
    constructor
    · intro hx _ _
      exact hx
    · intro hall
      exact hall [] (by simp)
  · rintro ⟨E, g, p, hE, hg, hspec⟩
    have hEc_coNP : Eᶜ ∈ PvsNP.coNP := by
      change (Eᶜ)ᶜ ∈ PvsNP.NP
      rwa [compl_compl]
    have hLc_eq : Lᶜ = ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ Eᶜ} : Language Bool) := by
      ext x
      change x ∉ L ↔ ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∉ E
      rw [hspec x]
      push Not
      rfl
    have hLc_NP : Lᶜ ∈ PvsNP.NP := by
      rw [hLc_eq]
      exact PvsNP.Units.m2_np_eq_conp_sigma2 hEq Eᶜ g p hEc_coNP hg
    have hL_coNP : L ∈ PvsNP.coNP := hLc_NP
    refine ⟨L, fun pair => pair.1, 0, hL_coNP, cpt_fst, fun x => ?_⟩
    constructor
    · intro hx
      exact ⟨[], by simp, hx⟩
    · rintro ⟨_, _, hx⟩
      exact hx

end PvsNP.Units.m2_np_eq_conp_sigma2_eq_pi2

theorem PvsNP.Units.m2_np_eq_conp_sigma2_eq_pi2 :
    PvsNP.NP = PvsNP.coNP → ∀ L : Language Bool,
      (∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
        E ∈ PvsNP.coNP ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
          ∀ x : List Bool, x ∈ L ↔ ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E) ↔
      ∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
        E ∈ PvsNP.NP ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
          ∀ x : List Bool, x ∈ L ↔ ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E :=
  PvsNP.Units.m2_np_eq_conp_sigma2_eq_pi2.main
