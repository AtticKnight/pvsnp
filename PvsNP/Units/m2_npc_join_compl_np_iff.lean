import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_conp_iff_join_compl
import PvsNP.Units.m2_npc_in_conp

/-- For an NP-complete language L, the join of L with its complement is in NP exactly when NP = coNP (TM2). -/
theorem PvsNP.Units.m2_npc_join_compl_np_iff :
    ∀ L : Language Bool, PvsNP.NPComplete L →
      (({x : List Bool | (∃ y ∈ L, x = false :: y) ∨ (∃ y ∈ Lᶜ, x = true :: y)} : Language Bool) ∈ PvsNP.NP ↔
        PvsNP.NP = PvsNP.coNP) :=
  fun L hL =>
    ⟨fun hJ => PvsNP.Units.m2_npc_in_conp L hL ((PvsNP.Units.m2_np_conp_iff_join_compl L).2 hJ).2,
     fun heq => (PvsNP.Units.m2_np_conp_iff_join_compl L).1 ⟨hL.1, heq ▸ hL.1⟩⟩
