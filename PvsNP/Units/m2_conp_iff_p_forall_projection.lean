import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_conp_verifier_iff

set_option autoImplicit false

namespace PvsNP.Units.m2_conp_iff_p_forall_projection

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem nonempty_in_p : ({y : List Bool | (!y.isEmpty) = true} : Language Bool) ∈ PvsNP.P :=
  ⟨fun y => !y.isEmpty, bf_cpt_neL, fun _ => Iff.rfl⟩

theorem main (L : Language Bool) : L ∈ PvsNP.coNP ↔
    ∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
      E ∈ PvsNP.P ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
        ∀ x : List Bool, x ∈ L ↔ ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E := by
  constructor
  · intro hL
    obtain ⟨V, p, hV, hmem⟩ := (PvsNP.Units.m2_conp_verifier_iff L).1 hL
    refine ⟨{y : List Bool | (!y.isEmpty) = true}, fun q => if V q then [true] else [], p,
      nonempty_in_p, cpt_bitFlag hV, fun x => ?_⟩
    rw [hmem x]
    refine forall_congr' fun c => imp_congr_right fun _ => ?_
    show V (x, c) = true ↔ (!(if V (x, c) then [true] else []).isEmpty) = true
    cases V (x, c) <;> decide
  · rintro ⟨E, g, p, ⟨d, hd, hdE⟩, hg, hmem⟩
    refine (PvsNP.Units.m2_conp_verifier_iff L).2 ⟨fun q => d (g q), p, cpt_comp hg hd, fun x => ?_⟩
    rw [hmem x]
    exact forall_congr' fun c => imp_congr_right fun _ => hdE (g (x, c))

end PvsNP.Units.m2_conp_iff_p_forall_projection

theorem PvsNP.Units.m2_conp_iff_p_forall_projection :
    ∀ L : Language Bool, L ∈ PvsNP.coNP ↔
      ∃ (E : Language Bool) (g : List Bool × List Bool → List Bool) (p : Polynomial ℕ),
        E ∈ PvsNP.P ∧ PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString g ∧
          ∀ x : List Bool, x ∈ L ↔ ∀ c : List Bool, c.length ≤ p.eval x.length → g (x, c) ∈ E :=
  PvsNP.Units.m2_conp_iff_p_forall_projection.main
