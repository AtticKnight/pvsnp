import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_reverse_polytime

/-! Original work for the make.fun desk campaign `pvsnp`, unit `m2_x_karp_reverse_preimage`. -/

set_option autoImplicit false

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal

theorem PvsNP.Units.m2_x_karp_reverse_preimage :
  ∀ L : Language Bool, PvsNP.KarpReducible L ({x : List Bool | x.reverse ∈ L} : Language Bool) ∧
  PvsNP.KarpReducible ({x : List Bool | x.reverse ∈ L} : Language Bool) L := by
  intro L
  refine ⟨⟨fun x => x.reverse, PvsNP.Units.m2_reverse_polytime, ?_⟩,
    ⟨fun x => x.reverse, PvsNP.Units.m2_reverse_polytime, ?_⟩⟩
  · intro x; show x ∈ L ↔ (x.reverse).reverse ∈ L; simp
  · intro x; show x.reverse ∈ L ↔ x.reverse ∈ L; rfl
