import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_lub
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_karp_trans

namespace PvsNP.Units.m2_join_assoc_karp

def Tag (A B : Language Bool) : Language Bool :=
  {x | (∃ y ∈ A, x = false :: y) ∨ (∃ y ∈ B, x = true :: y)}

end PvsNP.Units.m2_join_assoc_karp

/-- Reduce the three summands through their tags and use the empty word as a no-instance of each target join. -/
theorem PvsNP.Units.m2_join_assoc_karp :
    ∀ L₁ L₂ L₃ : Language Bool,
  PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool), x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool)
      ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool), x = true :: y)} : Language Bool) ∧
    PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool), x = true :: y)} : Language Bool)
      ({x : List Bool | (∃ y ∈ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool), x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool) := by
  intro A B C
  let tag := PvsNP.Units.m2_join_assoc_karp.Tag
  let ab := tag A B
  let bc := tag B C
  let left := tag ab C
  let right := tag A bc
  have noTag (X Y : Language Bool) : ∃ w : List Bool, w ∉ tag X Y := by
    refine ⟨[], ?_⟩
    change ¬ ((∃ y ∈ X, ([] : List Bool) = false :: y) ∨ (∃ y ∈ Y, ([] : List Bool) = true :: y))
    rintro (⟨y, _, h⟩ | ⟨y, _, h⟩) <;> cases h
  have noL : ∃ x : List Bool, x ∉ left := noTag ab C
  have noR : ∃ x : List Bool, x ∉ right := noTag A bc
  have IA := PvsNP.Units.m2_join_karp_sides A B
  have IB := PvsNP.Units.m2_join_karp_sides B C
  have IL := PvsNP.Units.m2_join_karp_sides ab C
  have IR := PvsNP.Units.m2_join_karp_sides A bc
  have br := PvsNP.Units.m2_karp_trans B bc right IB.1 IR.2
  have cr := PvsNP.Units.m2_karp_trans C bc right IB.2 IR.2
  have al := PvsNP.Units.m2_karp_trans A ab left IA.1 IL.1
  have bl := PvsNP.Units.m2_karp_trans B ab left IA.2 IL.1
  exact ⟨PvsNP.Units.m2_join_lub ab C right (PvsNP.Units.m2_join_lub A B right IR.1 br noR) cr noR,
    PvsNP.Units.m2_join_lub A bc left al (PvsNP.Units.m2_join_lub B C left bl IL.2 noL) noL⟩
