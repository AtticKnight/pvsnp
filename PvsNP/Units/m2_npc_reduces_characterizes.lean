import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_compl_iff
import PvsNP.Units.m2_np_down_closed

/-- Use completeness in the forward direction and polynomial preimages in the reverse direction, then complement both languages. -/
theorem PvsNP.Units.m2_npc_reduces_characterizes :
    ∀ L₀ : Language Bool, PvsNP.NPComplete L₀ → ∀ L : Language Bool,
  (L ∈ PvsNP.NP ↔ PvsNP.KarpReducible L L₀) ∧ (L ∈ PvsNP.coNP ↔ PvsNP.KarpReducible L L₀ᶜ) := by
  intro A hA L
  have np (B : Language Bool) : B ∈ PvsNP.NP ↔ PvsNP.KarpReducible B A :=
    ⟨hA.2 B, fun r => PvsNP.Units.m2_np_down_closed B A r hA.1⟩
  refine ⟨np L, ?_⟩
  change Lᶜ ∈ PvsNP.NP ↔ PvsNP.KarpReducible L Aᶜ
  have equiv := PvsNP.Units.m2_karp_compl_iff Lᶜ A
  simpa only [compl_compl] using (np Lᶜ).trans equiv
