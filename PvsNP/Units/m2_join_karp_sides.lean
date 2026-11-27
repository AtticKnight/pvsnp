import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp (Apache License
2.0), which this file imports: its machines are those of github.com/brilliant-hq/pequalnp-proofs
at commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0).
-/

namespace PvsNP.Units.m2_join_karp_sides

/-- Writing a fixed bit in front of the input is polynomial-time. -/
theorem cpt_cons (b : Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => b :: x) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_app2 (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const [b]) PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id

end PvsNP.Units.m2_join_karp_sides

/-- Each side of a join reduces to the join (TM2): write the side's bit in front. -/
theorem PvsNP.Units.m2_join_karp_sides :
    ∀ L₁ L₂ : Language Bool,
      PvsNP.KarpReducible L₁ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ∧
        PvsNP.KarpReducible L₂ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) := by
  intro L₁ L₂
  refine ⟨⟨fun x => false :: x, PvsNP.Units.m2_join_karp_sides.cpt_cons false, fun x => ?_⟩,
    ⟨fun x => true :: x, PvsNP.Units.m2_join_karp_sides.cpt_cons true, fun x => ?_⟩⟩
  · show x ∈ L₁ ↔ (∃ y ∈ L₁, false :: x = false :: y) ∨ (∃ y ∈ L₂, false :: x = true :: y)
    simp
  · show x ∈ L₂ ↔ (∃ y ∈ L₁, true :: x = false :: y) ∨ (∃ y ∈ L₂, true :: x = true :: y)
    simp
