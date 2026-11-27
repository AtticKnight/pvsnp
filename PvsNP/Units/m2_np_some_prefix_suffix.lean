import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_concat
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_subset_np

/-
A list has a prefix (suffix) in L exactly when it splits as u ++ v with u in L and v arbitrary
(u arbitrary and v in L), so both languages are concatenations with the universal language.
-/

namespace PvsNP.Units.m2_np_some_prefix_suffix

theorem prefix_eq (L : Language Bool) :
    ({x : List Bool | ∃ y : List Bool, y <+: x ∧ y ∈ L} : Language Bool) =
      {x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ∈ L ∧ v ∈ (Set.univ : Set (List Bool))} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, and_true]
  constructor
  · rintro ⟨y, ⟨t, h⟩, hy⟩
    exact ⟨y, t, h.symm, hy⟩
  · rintro ⟨u, v, rfl, hu⟩
    exact ⟨u, ⟨v, rfl⟩, hu⟩

theorem suffix_eq (L : Language Bool) :
    ({x : List Bool | ∃ y : List Bool, y <:+ x ∧ y ∈ L} : Language Bool) =
      {x : List Bool | ∃ u v : List Bool, x = u ++ v ∧ u ∈ (Set.univ : Set (List Bool)) ∧ v ∈ L} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, true_and]
  constructor
  · rintro ⟨y, ⟨s, h⟩, hy⟩
    exact ⟨s, y, h.symm, hy⟩
  · rintro ⟨u, v, rfl, hv⟩
    exact ⟨v, ⟨u, rfl⟩, hv⟩

end PvsNP.Units.m2_np_some_prefix_suffix

theorem PvsNP.Units.m2_np_some_prefix_suffix :
    ∀ L ∈ PvsNP.NP,
      ({x : List Bool | ∃ y : List Bool, y <+: x ∧ y ∈ L} : Language Bool) ∈ PvsNP.NP ∧
        ({x : List Bool | ∃ y : List Bool, y <:+ x ∧ y ∈ L} : Language Bool) ∈ PvsNP.NP := by
  intro L hL
  have hu : (Set.univ : Set (List Bool)) ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np (PvsNP.Units.m2_p_trivial.2)
  rw [PvsNP.Units.m2_np_some_prefix_suffix.prefix_eq, PvsNP.Units.m2_np_some_prefix_suffix.suffix_eq]
  exact ⟨PvsNP.Units.m2_np_concat _ _ hL hu, PvsNP.Units.m2_np_concat _ _ hu hL⟩
