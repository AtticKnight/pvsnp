import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_const_polytime

theorem PvsNP.Units.m2_karp_from_trivial :
    ∀ L : Language Bool,
      (PvsNP.KarpReducible ({x : List Bool | False} : Language Bool) L ↔ ∃ y : List Bool, y ∉ L) ∧
        (PvsNP.KarpReducible ({x : List Bool | True} : Language Bool) L ↔ ∃ y : List Bool, y ∈ L) := by
  intro L
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨f, _, hf⟩
    exact ⟨f [], fun h => (hf []).mpr h⟩
  · rintro ⟨y, hy⟩
    exact ⟨fun _ => y, PvsNP.Units.m2_const_polytime y, fun x => ⟨fun h => h.elim, fun h => (hy h).elim⟩⟩
  · rintro ⟨f, _, hf⟩
    exact ⟨f [], (hf []).mp trivial⟩
  · rintro ⟨y, hy⟩
    exact ⟨fun _ => y, PvsNP.Units.m2_const_polytime y, fun x => ⟨fun _ => hy, fun _ => trivial⟩⟩
