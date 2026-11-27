import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_finite_patch_classes
import PvsNP.Units.m2_karp_finite_patch

/-
Built on the settled units PvsNP.Units.fr_ladner (`cpt_id`), m2_polytime_comp,
m2_finite_patch_classes, and m2_karp_finite_patch of github.com/makedotfun/pvsnp
(Apache License 2.0).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_npc_finite_patch

open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

theorem main :
    ∀ (L L' : Language Bool) (S : Finset (List Bool)),
      (∀ x : List Bool, x ∉ S → (x ∈ L ↔ x ∈ L')) →
      (∃ y : List Bool, y ∈ L') →
      (∃ z : List Bool, z ∉ L') →
      PvsNP.NPComplete L → PvsNP.NPComplete L' := by
  intro L L' S hagree hy hz hL
  refine ⟨(PvsNP.Units.m2_finite_patch_classes L L' S hagree).2.1 hL.1, ?_⟩
  have hRefl : PvsNP.KarpReducible L' L' :=
    ⟨id, cpt_id, fun _ => Iff.rfl⟩
  have hLL' : PvsNP.KarpReducible L L' :=
    PvsNP.Units.m2_karp_finite_patch L' L L' S hRefl hy hz (fun x hx => (hagree x hx).symm)
  obtain ⟨g, hg, hg_red⟩ := hLL'
  intro A hA
  obtain ⟨f, hf, hf_red⟩ := hL.2 A hA
  refine ⟨g ∘ f, PvsNP.Units.m2_polytime_comp _ _ _ _ _ hf hg, fun x => ?_⟩
  exact (hf_red x).trans (hg_red (f x))

end PvsNP.Units.m2_npc_finite_patch

theorem PvsNP.Units.m2_npc_finite_patch :
    ∀ (L L' : Language Bool) (S : Finset (List Bool)),
      (∀ x : List Bool, x ∉ S → (x ∈ L ↔ x ∈ L')) →
      (∃ y : List Bool, y ∈ L') →
      (∃ z : List Bool, z ∉ L') →
      PvsNP.NPComplete L → PvsNP.NPComplete L' :=
  PvsNP.Units.m2_npc_finite_patch.main
