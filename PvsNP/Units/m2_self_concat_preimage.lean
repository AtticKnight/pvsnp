import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_pair_fun_specialize
import PvsNP.Units.m2_p_down_closed
import PvsNP.Units.m2_np_down_closed
import PvsNP.Units.m2_conp_down_closed

/-- P, NP and coNP are closed under taking the strings whose square xx is in L (TM2).

The map x ↦ x ++ x is polynomial-time: append on pairs (the third part of the settled unit
m2_pair_split_polytime) specialised to both arguments x (the settled unit
m2_pair_fun_specialize). The language {x | x ++ x ∈ L} therefore Karp-reduces to L, and the
three down-closure lemmas (m2_p_down_closed, m2_np_down_closed, m2_conp_down_closed) carry
membership in P, NP and coNP along the reduction. -/
theorem PvsNP.Units.m2_self_concat_preimage :
    ∀ L : Language Bool,
      (L ∈ PvsNP.P → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.P) ∧
        (L ∈ PvsNP.NP → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.NP) ∧
          (L ∈ PvsNP.coNP → ({x : List Bool | x ++ x ∈ L} : Language Bool) ∈ PvsNP.coNP) := by
  intro L
  have hself : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x ++ x) :=
    (PvsNP.Units.m2_pair_fun_specialize (fun p : List Bool × List Bool => p.1 ++ p.2) []
      PvsNP.Units.m2_pair_split_polytime.2.2).2.2
  have hred : PvsNP.KarpReducible ({x : List Bool | x ++ x ∈ L} : Language Bool) L :=
    ⟨fun x : List Bool => x ++ x, hself, fun x => Iff.rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hL
    exact PvsNP.Units.m2_p_down_closed _ _ hred hL
  · intro hL
    exact PvsNP.Units.m2_np_down_closed _ _ hred hL
  · intro hL
    exact PvsNP.Units.m2_conp_down_closed _ _ hred hL
