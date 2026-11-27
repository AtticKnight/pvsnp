import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_union

namespace PvsNP.Units.m2_p_list_union

/-- The union over a list of languages, split off its head: it is the head language together
with the union over the tail. -/
theorem union_cons (L : Language Bool) (Ls : List (Language Bool)) :
    ({x : List Bool | ∃ L' ∈ L :: Ls, x ∈ L'} : Language Bool) =
      L ⊔ {x : List Bool | ∃ L' ∈ Ls, x ∈ L'} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, List.mem_cons]
  constructor
  · rintro ⟨L', (rfl | hL'), hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨L', hL', hx⟩
  · rintro (hx | ⟨L', hL', hx⟩)
    · exact ⟨L, Or.inl rfl, hx⟩
    · exact ⟨L', Or.inr hL', hx⟩

/-- The union over the empty list of languages is the empty language. -/
theorem union_nil :
    ({x : List Bool | ∃ L ∈ ([] : List (Language Bool)), x ∈ L} : Language Bool) = ∅ := by
  ext x
  simp

end PvsNP.Units.m2_p_list_union

/-- P is closed under finite unions: the union of a list of languages in P is in P. -/
theorem PvsNP.Units.m2_p_list_union :
    ∀ Ls : List (Language Bool), (∀ L ∈ Ls, L ∈ PvsNP.P) →
      ({x : List Bool | ∃ L ∈ Ls, x ∈ L} : Language Bool) ∈ PvsNP.P := by
  intro Ls
  induction Ls with
  | nil =>
    intro _
    rw [PvsNP.Units.m2_p_list_union.union_nil]
    exact PvsNP.Units.m2_p_trivial.1
  | cons L Ls ih =>
    intro h
    have hL : L ∈ PvsNP.P := h L List.mem_cons_self
    have hLs : ∀ L' ∈ Ls, L' ∈ PvsNP.P := fun L' hL' => h L' (List.mem_cons_of_mem _ hL')
    rw [PvsNP.Units.m2_p_list_union.union_cons]
    exact PvsNP.Units.m2_p_union L _ hL (ih hLs)
