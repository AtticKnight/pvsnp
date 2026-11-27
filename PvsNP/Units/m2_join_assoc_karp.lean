import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_join_lub
import PvsNP.Units.m2_karp_trans

set_option autoImplicit false

namespace PvsNP.Units.m2_join_assoc_karp

private theorem nil_not_mem_join (A B : Language Bool) :
    ∃ z : List Bool, z ∉ ({x : List Bool | (∃ y ∈ A, x = false :: y) ∨ (∃ y ∈ B, x = true :: y)} : Language Bool) := by
  refine ⟨[], ?_⟩
  rintro (⟨_, _, h⟩ | ⟨_, _, h⟩) <;> cases h

theorem main (L₁ L₂ L₃ : Language Bool) :
    PvsNP.KarpReducible
        ({x : List Bool | (∃ y ∈ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool), x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool)
        ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool), x = true :: y)} : Language Bool) ∧
      PvsNP.KarpReducible
        ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool), x = true :: y)} : Language Bool)
        ({x : List Bool | (∃ y ∈ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool), x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool) := by
  let L12 : Language Bool := {x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)}
  let L23 : Language Bool := {x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)}
  let JL : Language Bool := {x : List Bool | (∃ y ∈ L12, x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)}
  let JR : Language Bool := {x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L23, x = true :: y)}
  have hL1_JR : PvsNP.KarpReducible L₁ JR :=
    (PvsNP.Units.m2_join_karp_sides L₁ L23).1
  have hL2_JR : PvsNP.KarpReducible L₂ JR :=
    PvsNP.Units.m2_karp_trans L₂ L23 JR
      (PvsNP.Units.m2_join_karp_sides L₂ L₃).1
      (PvsNP.Units.m2_join_karp_sides L₁ L23).2
  have hL3_JR : PvsNP.KarpReducible L₃ JR :=
    PvsNP.Units.m2_karp_trans L₃ L23 JR
      (PvsNP.Units.m2_join_karp_sides L₂ L₃).2
      (PvsNP.Units.m2_join_karp_sides L₁ L23).2
  have hL12_JR : PvsNP.KarpReducible L12 JR :=
    PvsNP.Units.m2_join_lub L₁ L₂ JR hL1_JR hL2_JR (nil_not_mem_join L₁ L23)
  have hLR : PvsNP.KarpReducible JL JR :=
    PvsNP.Units.m2_join_lub L12 L₃ JR hL12_JR hL3_JR (nil_not_mem_join L₁ L23)
  have hL1_JL : PvsNP.KarpReducible L₁ JL :=
    PvsNP.Units.m2_karp_trans L₁ L12 JL
      (PvsNP.Units.m2_join_karp_sides L₁ L₂).1
      (PvsNP.Units.m2_join_karp_sides L12 L₃).1
  have hL2_JL : PvsNP.KarpReducible L₂ JL :=
    PvsNP.Units.m2_karp_trans L₂ L12 JL
      (PvsNP.Units.m2_join_karp_sides L₁ L₂).2
      (PvsNP.Units.m2_join_karp_sides L12 L₃).1
  have hL3_JL : PvsNP.KarpReducible L₃ JL :=
    (PvsNP.Units.m2_join_karp_sides L12 L₃).2
  have hL23_JL : PvsNP.KarpReducible L23 JL :=
    PvsNP.Units.m2_join_lub L₂ L₃ JL hL2_JL hL3_JL (nil_not_mem_join L12 L₃)
  have hRL : PvsNP.KarpReducible JR JL :=
    PvsNP.Units.m2_join_lub L₁ L23 JL hL1_JL hL23_JL (nil_not_mem_join L12 L₃)
  exact ⟨hLR, hRL⟩

end PvsNP.Units.m2_join_assoc_karp

/-- The join is associative up to Karp reductions in both directions (TM2). -/
theorem PvsNP.Units.m2_join_assoc_karp :
    ∀ L₁ L₂ L₃ : Language Bool,
      PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool), x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool)
          ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool), x = true :: y)} : Language Bool) ∧
        PvsNP.KarpReducible ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool), x = true :: y)} : Language Bool)
          ({x : List Bool | (∃ y ∈ ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool), x = false :: y) ∨ (∃ y ∈ L₃, x = true :: y)} : Language Bool) :=
  PvsNP.Units.m2_join_assoc_karp.main
