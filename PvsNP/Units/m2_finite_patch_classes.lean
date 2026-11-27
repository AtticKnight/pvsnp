import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_union
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_np_union
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_conp_union
import PvsNP.Units.m2_conp_inter

/-
Original proof of `PvsNP.Units.m2_finite_patch_classes`, from the settled units it imports. With
`F` the finite set `S` and `A` the finite set of members of `S` that lie in `L'`,
`L' = (L ⊓ Fᶜ) ⊔ A`. `F`, `Fᶜ` and `A` are in P (`m2_p_finite`, `m2_p_compl`), hence in NP
(`m2_p_subset_np`) and, a language in P having its complement in P, in coNP. Each class is closed
under `⊓` and `⊔` (`m2_p_inter`, `m2_p_union`, `m2_np_inter`, `m2_np_union`, `m2_conp_inter`,
`m2_conp_union`).
-/

namespace PvsNP.Units.m2_finite_patch_classes

open Classical in
/-- `L'` rebuilt from `L` and two finite sets. -/
theorem patch_eq (L L' : Language Bool) (S : Finset (List Bool))
    (h : ∀ x : List Bool, x ∉ S → (x ∈ L ↔ x ∈ L')) :
    L' = (L ⊓ ({x : List Bool | x ∈ S} : Language Bool)ᶜ) ⊔
      ({x : List Bool | x ∈ S.filter (fun y => y ∈ L')} : Language Bool) := by
  ext x
  show x ∈ L' ↔ (x ∈ L ∧ x ∉ S) ∨ x ∈ S.filter (fun y => y ∈ L')
  rw [Finset.mem_filter]
  by_cases hx : x ∈ S
  · simp [hx]
  · simp [hx, h x hx]

/-- A language in P is in coNP. -/
theorem p_in_conp (X : Language Bool) (hX : X ∈ PvsNP.P) : X ∈ PvsNP.coNP :=
  PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_p_compl X hX)

end PvsNP.Units.m2_finite_patch_classes

open Classical in
theorem PvsNP.Units.m2_finite_patch_classes :
    ∀ (L L' : Language Bool) (S : Finset (List Bool)), (∀ x : List Bool, x ∉ S → (x ∈ L ↔ x ∈ L')) →
      (L ∈ PvsNP.P → L' ∈ PvsNP.P) ∧ (L ∈ PvsNP.NP → L' ∈ PvsNP.NP) ∧
        (L ∈ PvsNP.coNP → L' ∈ PvsNP.coNP) := by
  intro L L' S h
  rw [PvsNP.Units.m2_finite_patch_classes.patch_eq L L' S h]
  have hF : ({x : List Bool | x ∈ S} : Language Bool)ᶜ ∈ PvsNP.P :=
    PvsNP.Units.m2_p_compl _ (PvsNP.Units.m2_p_finite S)
  have hA : ({x : List Bool | x ∈ S.filter (fun y => y ∈ L')} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_p_finite _
  refine ⟨fun hL => ?_, fun hL => ?_, fun hL => ?_⟩
  · exact PvsNP.Units.m2_p_union _ _ (PvsNP.Units.m2_p_inter _ _ hL hF) hA
  · exact PvsNP.Units.m2_np_union _ _
      (PvsNP.Units.m2_np_inter _ _ hL (PvsNP.Units.m2_p_subset_np hF))
      (PvsNP.Units.m2_p_subset_np hA)
  · exact PvsNP.Units.m2_conp_union _ _
      (PvsNP.Units.m2_conp_inter _ _ hL (PvsNP.Units.m2_finite_patch_classes.p_in_conp _ hF))
      (PvsNP.Units.m2_finite_patch_classes.p_in_conp _ hA)
