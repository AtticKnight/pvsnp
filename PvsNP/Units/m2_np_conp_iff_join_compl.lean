import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_join_in_p
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_np_union
import PvsNP.Units.m2_p_subset_np

/-!
`L` is in `NP ∩ coNP` exactly when the join of `L` with its complement is in `NP`.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_np_conp_iff_join_compl

theorem tail_in_np {L : Language Bool} (hL : L ∈ PvsNP.NP) :
    ({x : List Bool | x.tail ∈ L} : Language Bool) ∈ PvsNP.NP := by
  refine PvsNP.Units.m2_np_down_closed
    ({x : List Bool | x.tail ∈ L} : Language Bool) L ?_ hL
  refine ⟨List.tail, ?_, fun _ => Iff.rfl⟩
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail

theorem cons_in_np (b : Bool) {L : Language Bool} (hL : L ∈ PvsNP.NP) :
    ({x : List Bool | ∃ y ∈ L, x = b :: y} : Language Bool) ∈ PvsNP.NP := by
  have hEq : ({x : List Bool | ∃ y ∈ L, x = b :: y} : Language Bool) =
      ({x : List Bool | ∃ y : List Bool, x = b :: y} : Language Bool) ⊓
      ({x : List Bool | x.tail ∈ L} : Language Bool) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, hy⟩
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact ⟨y, hy, rfl⟩
  rw [hEq]
  exact PvsNP.Units.m2_np_inter _ _
    (PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_join_in_p.head_in_p b))
    (tail_in_np hL)

theorem join_in_np {L₁ L₂ : Language Bool}
    (h₁ : L₁ ∈ PvsNP.NP) (h₂ : L₂ ∈ PvsNP.NP) :
    ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ∈
      PvsNP.NP := by
  have hEq :
      ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) =
        ({x : List Bool | ∃ y ∈ L₁, x = false :: y} : Language Bool) ⊔
        ({x : List Bool | ∃ y ∈ L₂, x = true :: y} : Language Bool) := by
    ext x
    rfl
  rw [hEq]
  exact PvsNP.Units.m2_np_union _ _ (cons_in_np false h₁) (cons_in_np true h₂)

end PvsNP.Units.m2_np_conp_iff_join_compl

theorem PvsNP.Units.m2_np_conp_iff_join_compl :
    ∀ L : Language Bool, L ∈ PvsNP.NP ∩ PvsNP.coNP ↔
      ({x : List Bool | (∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ Lᶜ, x = true :: y)} : Language Bool) ∈
        PvsNP.NP := by
  intro L
  constructor
  · intro h
    exact PvsNP.Units.m2_np_conp_iff_join_compl.join_in_np h.1 h.2
  · intro hJ
    obtain ⟨hL, hLc⟩ := PvsNP.Units.m2_join_karp_sides L Lᶜ
    exact ⟨PvsNP.Units.m2_np_down_closed L _ hL hJ,
      PvsNP.Units.m2_np_down_closed Lᶜ _ hLc hJ⟩
