import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_finite_patch_classes

theorem PvsNP.Units.m2_z_finset_patch_classes :
    ∀ (L : Language Bool) (S : Finset (List Bool)),
      (L ∈ PvsNP.P → ({x : List Bool | x ∈ S ∨ x ∈ L} : Language Bool) ∈ PvsNP.P ∧
          ({x : List Bool | x ∈ L ∧ x ∉ S} : Language Bool) ∈ PvsNP.P) ∧
        (L ∈ PvsNP.NP → ({x : List Bool | x ∈ S ∨ x ∈ L} : Language Bool) ∈ PvsNP.NP ∧
          ({x : List Bool | x ∈ L ∧ x ∉ S} : Language Bool) ∈ PvsNP.NP) ∧
        (L ∈ PvsNP.coNP → ({x : List Bool | x ∈ S ∨ x ∈ L} : Language Bool) ∈ PvsNP.coNP ∧
          ({x : List Bool | x ∈ L ∧ x ∉ S} : Language Bool) ∈ PvsNP.coNP) := by
  intro L S
  have hA : ∀ x : List Bool, x ∉ S →
      (x ∈ L ↔ x ∈ ({x : List Bool | x ∈ S ∨ x ∈ L} : Language Bool)) := by
    intro x hx
    show x ∈ L ↔ x ∈ S ∨ x ∈ L
    exact ⟨Or.inr, fun h => h.elim (fun hs => absurd hs hx) id⟩
  have hB : ∀ x : List Bool, x ∉ S →
      (x ∈ L ↔ x ∈ ({x : List Bool | x ∈ L ∧ x ∉ S} : Language Bool)) := by
    intro x hx
    show x ∈ L ↔ x ∈ L ∧ x ∉ S
    exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
  have h1 := PvsNP.Units.m2_finite_patch_classes L _ S hA
  have h2 := PvsNP.Units.m2_finite_patch_classes L _ S hB
  exact ⟨fun hL => ⟨h1.1 hL, h2.1 hL⟩,
    fun hL => ⟨h1.2.1 hL, h2.2.1 hL⟩,
    fun hL => ⟨h1.2.2 hL, h2.2.2 hL⟩⟩
