import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_union
import PvsNP.Units.m2_p_inter
import PvsNP.Units.m2_np_union
import PvsNP.Units.m2_np_inter

/-- Tally languages of a union and an intersection stay in P, and in NP, when
those of the two sets are: the tally language of `A ∪ B` is the union of the two
tally languages and that of `A ∩ B` their intersection (a tally string
`List.replicate n true` determines `n` by its length), so the settled closure
units `m2_p_union`, `m2_p_inter`, `m2_np_union` and `m2_np_inter` finish. -/
theorem PvsNP.Units.m2_z_tally_union_inter :
    ∀ A B : Set ℕ,
      (({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) ∈ PvsNP.P → ({x : List Bool | ∃ n ∈ B, x = List.replicate n true} : Language Bool) ∈ PvsNP.P →
          ({x : List Bool | ∃ n ∈ (A ∪ B), x = List.replicate n true} : Language Bool) ∈ PvsNP.P ∧ ({x : List Bool | ∃ n ∈ (A ∩ B), x = List.replicate n true} : Language Bool) ∈ PvsNP.P) ∧
        (({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) ∈ PvsNP.NP → ({x : List Bool | ∃ n ∈ B, x = List.replicate n true} : Language Bool) ∈ PvsNP.NP →
          ({x : List Bool | ∃ n ∈ (A ∪ B), x = List.replicate n true} : Language Bool) ∈ PvsNP.NP ∧ ({x : List Bool | ∃ n ∈ (A ∩ B), x = List.replicate n true} : Language Bool) ∈ PvsNP.NP) := by
  intro A B
  have hU : ({x : List Bool | ∃ n ∈ (A ∪ B), x = List.replicate n true} : Language Bool)
      = ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) ∪
        ({x : List Bool | ∃ n ∈ B, x = List.replicate n true} : Language Bool) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨n, hn, rfl⟩
      cases hn with
      | inl h => exact Or.inl ⟨n, h, rfl⟩
      | inr h => exact Or.inr ⟨n, h, rfl⟩
    · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
      · exact ⟨n, Or.inl hn, rfl⟩
      · exact ⟨n, Or.inr hn, rfl⟩
  have hI : ({x : List Bool | ∃ n ∈ (A ∩ B), x = List.replicate n true} : Language Bool)
      = ({x : List Bool | ∃ n ∈ A, x = List.replicate n true} : Language Bool) ∩
        ({x : List Bool | ∃ n ∈ B, x = List.replicate n true} : Language Bool) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn.1, rfl⟩, ⟨n, hn.2, rfl⟩⟩
    · rintro ⟨⟨n₁, hn₁, rfl⟩, ⟨n₂, hn₂, h2⟩⟩
      have hnl : n₁ = n₂ := by
        have hl := congrArg List.length h2
        simp only [List.length_replicate] at hl
        exact hl
      subst hnl
      exact ⟨_, ⟨hn₁, hn₂⟩, rfl⟩
  constructor
  · intro hA hB
    constructor
    · rw [hU]
      exact PvsNP.Units.m2_p_union _ _ hA hB
    · rw [hI]
      exact PvsNP.Units.m2_p_inter _ _ hA hB
  · intro hA hB
    constructor
    · rw [hU]
      exact PvsNP.Units.m2_np_union _ _ hA hB
    · rw [hI]
      exact PvsNP.Units.m2_np_inter _ _ hA hB
