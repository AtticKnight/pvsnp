import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_subset_np

/-- An NP-hard language is neither empty nor all strings: the empty and the universal
language are both in NP (the settled units `m2_p_trivial` and `m2_p_subset_np`), so each
Karp-reduces to `L`; look at where the reductions send the empty string. -/
theorem PvsNP.Units.m2_nphard_nontrivial :
    ∀ L : Language Bool, PvsNP.NPHard L → (∃ y : List Bool, y ∈ L) ∧ ∃ z : List Bool, z ∉ L := by
  intro L hL
  have hEmpty : (∅ : Set (List Bool)) ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np PvsNP.Units.m2_p_trivial.1
  have hUniv : (Set.univ : Set (List Bool)) ∈ PvsNP.NP :=
    PvsNP.Units.m2_p_subset_np PvsNP.Units.m2_p_trivial.2
  obtain ⟨f, _hf, hfred⟩ := hL _ hUniv
  obtain ⟨g, _hg, hgred⟩ := hL _ hEmpty
  refine ⟨⟨f [], (hfred []).mp (Set.mem_univ [])⟩, ⟨g [], ?_⟩⟩
  intro hg
  have hmem : [] ∈ (∅ : Set (List Bool)) := (hgred []).mpr hg
  simp at hmem
