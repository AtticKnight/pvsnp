import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_karp_trans
import PvsNP.Units.m2_np_reverse_closed
import PvsNP.Units.m2_reverse_polytime

open PvsNP.Units

/-- Reverse is a polynomial-time involution, so the preimage of a complete
language under reverse is again complete. -/
theorem PvsNP.Units.m2_npc_reverse :
    ∀ L : Language Bool, PvsNP.NPComplete L →
      PvsNP.NPComplete ({x : List Bool | x.reverse ∈ L} : Language Bool) := by
  intro L hComplete
  refine ⟨m2_np_reverse_closed L hComplete.1, ?_⟩
  have reduction : PvsNP.KarpReducible L {x : List Bool | x.reverse ∈ L} := by
    refine ⟨List.reverse, m2_reverse_polytime, fun x => ?_⟩
    change x ∈ L ↔ x.reverse.reverse ∈ L
    simp
  intro A hA
  exact m2_karp_trans _ _ _ (hComplete.2 A hA) reduction
