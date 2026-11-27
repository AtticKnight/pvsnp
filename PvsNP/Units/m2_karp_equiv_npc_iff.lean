import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_trans
import PvsNP.Units.m2_np_down_closed

/-- Compose each hardness witness with the forward reduction. Pull membership back along the reverse reduction. -/
theorem PvsNP.Units.m2_karp_equiv_npc_iff :
    ∀ L₁ L₂ : Language Bool, PvsNP.KarpReducible L₁ L₂ → PvsNP.KarpReducible L₂ L₁ →
  (PvsNP.NPHard L₁ ↔ PvsNP.NPHard L₂) ∧ (PvsNP.NPComplete L₁ ↔ PvsNP.NPComplete L₂) := by
  intro A B ab ba
  have hard : PvsNP.NPHard A ↔ PvsNP.NPHard B :=
    ⟨fun ha L hL => PvsNP.Units.m2_karp_trans L A B (ha L hL) ab,
     fun hb L hL => PvsNP.Units.m2_karp_trans L B A (hb L hL) ba⟩
  refine ⟨hard, ?_⟩
  constructor
  · intro h
    exact ⟨PvsNP.Units.m2_np_down_closed B A ba h.1, hard.1 h.2⟩
  · intro h
    exact ⟨PvsNP.Units.m2_np_down_closed A B ab h.1, hard.2 h.2⟩
