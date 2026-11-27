import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_pair_split_polytime

/-- `NP = coNP` exactly when the second level `Π₂` of the polynomial hierarchy is in `coNP` (TM2). -/
theorem PvsNP.Units.m2_np_eq_conp_iff_pi2_conp :
    PvsNP.NP = PvsNP.coNP ↔ ∀ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.NP → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g →
        ({x : List Bool | ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E} : Language Bool) ∈ PvsNP.coNP := by
  constructor
  · intro h E g p hE hg
    have hEc_co : Eᶜ ∈ PvsNP.coNP := by
      show Eᶜᶜ ∈ PvsNP.NP
      rwa [compl_compl]
    have hEc_np : Eᶜ ∈ PvsNP.NP := by
      rwa [h]
    have hP : ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ Eᶜ} :
        Language Bool) ∈ PvsNP.NP :=
      PvsNP.Units.m2_np_projection Eᶜ g p hEc_np hg
    show ({x : List Bool | ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E} :
        Language Bool)ᶜ ∈ PvsNP.NP
    have hS : ({x : List Bool | ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E} :
        Language Bool)ᶜ =
        ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ Eᶜ} :
        Language Bool) := by
      ext x
      show (¬∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E) ↔
        ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∉ E
      push_neg
      rfl
    rw [hS]
    exact hP
  · intro h
    have hsub : PvsNP.NP ⊆ PvsNP.coNP := by
      intro E hE
      have hmem := h E (fun q : List Bool × List Bool => q.1) 0 hE
        PvsNP.Units.m2_pair_split_polytime.1
      have hset : ({x : List Bool | ∀ c : List Bool, c.length ≤ (0 : Polynomial ℕ).eval x.length →
          (fun q : List Bool × List Bool => q.1) (x, c) ∈ E} : Language Bool) = E := by
        ext x
        show (∀ c : List Bool, c.length ≤ (0 : Polynomial ℕ).eval x.length → x ∈ E) ↔ x ∈ E
        exact ⟨fun hf => hf [] (by simp), fun hx _ _ => hx⟩
      rwa [hset] at hmem
    refine Set.Subset.antisymm hsub (fun L hL => ?_)
    have hLc : Lᶜ ∈ PvsNP.NP := hL
    have hLcc : Lᶜᶜ ∈ PvsNP.NP := hsub hLc
    rwa [compl_compl] at hLcc
