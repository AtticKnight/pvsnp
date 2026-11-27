import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_join_in_p
import PvsNP.Units.m2_join_karp_sides
import PvsNP.Units.m2_npc_transfer
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_np_inter
import PvsNP.Units.m2_np_union
import PvsNP.Units.m2_p_subset_np

namespace PvsNP.Units.m2_npc_join

lemma tail_in_np {L : Language Bool} (hL : L ∈ PvsNP.NP) :
    ({x : List Bool | x.tail ∈ L} : Language Bool) ∈ PvsNP.NP := by
  refine PvsNP.Units.m2_np_down_closed _ L ⟨List.tail, ?_, fun x => Iff.rfl⟩ hL
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail

lemma cons_in_np (b : Bool) {L : Language Bool} (hL : L ∈ PvsNP.NP) :
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
    (PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_join_in_p.head_in_p b)) (tail_in_np hL)

lemma join_in_np {A B : Language Bool} (hA : A ∈ PvsNP.NP) (hB : B ∈ PvsNP.NP) :
    ({x : List Bool | (∃ y ∈ A, x = false :: y) ∨ (∃ y ∈ B, x = true :: y)} : Language Bool) ∈ PvsNP.NP :=
  PvsNP.Units.m2_np_union _ _ (cons_in_np false hA) (cons_in_np true hB)

end PvsNP.Units.m2_npc_join

theorem PvsNP.Units.m2_npc_join :
    ∀ L₁ L₂ : Language Bool, PvsNP.NPComplete L₁ → L₂ ∈ PvsNP.NP →
      PvsNP.NPComplete ({x : List Bool | (∃ y ∈ L₁, x = false :: y) ∨ (∃ y ∈ L₂, x = true :: y)} : Language Bool) ∧
        PvsNP.NPComplete ({x : List Bool | (∃ y ∈ L₂, x = false :: y) ∨ (∃ y ∈ L₁, x = true :: y)} : Language Bool) := by
  intro L₁ L₂ h₁ h₂
  exact ⟨PvsNP.Units.m2_npc_transfer _ _ h₁ (PvsNP.Units.m2_npc_join.join_in_np h₁.1 h₂)
      (PvsNP.Units.m2_join_karp_sides L₁ L₂).1,
    PvsNP.Units.m2_npc_transfer _ _ h₁ (PvsNP.Units.m2_npc_join.join_in_np h₂ h₁.1)
      (PvsNP.Units.m2_join_karp_sides L₂ L₁).2⟩
