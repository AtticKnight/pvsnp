import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection

/-- coNP is closed under bounded universal projection: the complement of the projected language
is the bounded existential projection of the complement of `E`, which is in NP. -/
theorem PvsNP.Units.m2_conp_forall_projection :
  ∀ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
    E ∈ PvsNP.coNP → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g →
      ({x : List Bool | ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E} : Language Bool) ∈ PvsNP.coNP := by
  intro E g p hE hg
  have h := PvsNP.Units.m2_np_projection Eᶜ g p hE hg
  have heq : ({x : List Bool | ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E} : Language Bool)ᶜ
      = {x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ Eᶜ} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, Set.mem_compl_iff]
    constructor
    · rintro ⟨c, hc, hn⟩
      exact ⟨c, hc, hn⟩
    · rintro ⟨c, hc, hn⟩
      exact ⟨c, hc, hn⟩
  exact (congrArg (fun S : Language Bool => S ∈ PvsNP.NP) heq).mpr h
