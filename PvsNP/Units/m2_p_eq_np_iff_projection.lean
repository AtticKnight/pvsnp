import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_np_projection
import PvsNP.Units.m2_p_subset_np

set_option autoImplicit false

/-- `P = NP` iff `P` is closed under polynomial-time bounded existential projection (TM2). -/
theorem PvsNP.Units.m2_p_eq_np_iff_projection :
    PvsNP.P = PvsNP.NP ↔ ∀ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.P → PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g →
        ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E} : Language Bool) ∈ PvsNP.P := by
  constructor
  · intro hEq E g p hE hg
    rw [hEq] at hE ⊢
    exact PvsNP.Units.m2_np_projection E g p hE hg
  · intro hProj
    apply Set.Subset.antisymm PvsNP.Units.m2_p_subset_np
    rintro L ⟨V, p, hV, hiff⟩
    let E : Language Bool := {s : List Bool | V (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB s) = true}
    have hEP : E ∈ PvsNP.P :=
      ⟨fun s => V (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB s),
        PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
          PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_unpairB hV,
        fun _ => Iff.rfl⟩
    let g : List Bool × List Bool → List Bool :=
      fun q => PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB q.1 q.2
    have hg : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g :=
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_pairB
    have hP := hProj E g p hEP hg
    have heq : ({x : List Bool | ∃ c : List Bool, c.length ≤ p.eval x.length ∧ g (x, c) ∈ E} : Language Bool) = L := by
      ext x
      change (∃ c : List Bool, c.length ≤ p.eval x.length ∧
        V (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB
          (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.pairB x c)) = true) ↔ x ∈ L
      simp only [PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.unpairB_pairB]
      exact (hiff x).symm
    rwa [heq] at hP
