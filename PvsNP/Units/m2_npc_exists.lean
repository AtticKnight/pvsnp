import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m1_sat_npcomplete_tm2
import PvsNP.Units.m1_flat_to_st
import PvsNP.Units.m1_flat_np_to_st_np
import PvsNP.Units.m1_st_np_to_flat_np
import PvsNP.Units.m1_st_to_tm2
import PvsNP.Units.m1_tm2_to_st
import PvsNP.Units.m2_npc_in_p

/-!
# m2_npc_exists

Proved from the settled units `m1_sat_npcomplete_tm2`, `m1_flat_to_st`, `m1_flat_np_to_st_np`, `m1_st_np_to_flat_np`, `m1_st_to_tm2`, `m1_tm2_to_st`, `m2_npc_in_p` of github.com/makedotfun/pvsnp
(commit fe00cce97615b933d953614d674245879348ec48), imported as the unit's allowed imports.
-/

namespace PvsNP.Units.m2_npc_exists


/-- Some language is NP-complete on TM2: SAT, as a language of bit strings. -/
theorem h_main : ∀ L : Language Bool, (∀ x, x ∈ L ↔ SATStr x) → PvsNP.NPComplete L :=
  (PvsNP.Units.m1_sat_npcomplete_tm2 PvsNP.Units.m1_flat_to_st (fun L => ⟨PvsNP.Units.m1_flat_np_to_st_np L, PvsNP.Units.m1_st_np_to_flat_np L⟩) (fun ea eb f => ⟨PvsNP.Units.m1_st_to_tm2 ea eb f, PvsNP.Units.m1_tm2_to_st ea eb f⟩))


/-- Some language is NP-complete on TM2: SAT, as a language of bit strings. -/
theorem h_exists : ∃ L : Language Bool, PvsNP.NPComplete L :=
  ⟨{x | SATStr x}, PvsNP.Units.m2_npc_exists.h_main _ (fun _ => Iff.rfl)⟩


/-- SAT is in NP on TM2. -/
theorem h_in_np : ∀ L : Language Bool, (∀ x, x ∈ L ↔ SATStr x) → L ∈ PvsNP.NP :=
  fun L hL => (PvsNP.Units.m2_npc_exists.h_main L hL).1


/-- P = NP exactly when SAT is in P (TM2). -/
theorem h_iff :
    PvsNP.P = PvsNP.NP ↔ ∀ L : Language Bool, (∀ x, x ∈ L ↔ SATStr x) → L ∈ PvsNP.P := by
  constructor
  · intro h L hL
    rw [h]
    exact (PvsNP.Units.m2_npc_exists.h_main L hL).1
  · intro h
    have hS := PvsNP.Units.m2_npc_exists.h_main {x | SATStr x} (fun _ => Iff.rfl)
    exact PvsNP.Units.m2_npc_in_p _ hS (h _ (fun _ => Iff.rfl))


end PvsNP.Units.m2_npc_exists

theorem PvsNP.Units.m2_npc_exists :
    ∃ L : Language Bool, PvsNP.NPComplete L :=
  PvsNP.Units.m2_npc_exists.h_exists
