import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite
import PvsNP.Units.m2_p_compl
import PvsNP.Units.m2_p_subset_np
import PvsNP.Units.m2_npc_in_p

/-!
An NP-hard language missing only finitely many strings makes P = NP.

Proof (following the hint): the complement of `L` is contained in the finite set `S`,
hence `Lᶜ` is the finite language `S.filter (· ∉ L)`, so `Lᶜ ∈ P` by `m2_p_finite`,
`L ∈ P` by `m2_p_compl` (double complement), `L ∈ NP` by `m2_p_subset_np`,
so `L` is NP-complete, and `m2_npc_in_p` gives `P = NP`.
-/

theorem PvsNP.Units.m2_nphard_cofinite_p_eq_np :
    ∀ (L : Language Bool) (S : Finset (List Bool)), PvsNP.NPHard L →
      (∀ x : List Bool, x ∉ L → x ∈ S) → PvsNP.P = PvsNP.NP := by
  intro L S hHard hCov
  classical
  -- The complement of L is exactly the finite language of S outside L.
  have hcompl : Lᶜ = {x : List Bool | x ∈ S.filter (fun x => x ∉ L)} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Finset.mem_filter]
    constructor
    · intro hx
      exact ⟨hCov x hx, hx⟩
    · intro h
      exact h.2
  -- Hence Lᶜ ∈ P.
  have hLcP : Lᶜ ∈ PvsNP.P := by
    rw [hcompl]
    exact PvsNP.Units.m2_p_finite (S.filter (fun x => x ∉ L))
  -- Hence L ∈ P, by closure of P under complement.
  have hLP : L ∈ PvsNP.P := by
    have h := PvsNP.Units.m2_p_compl Lᶜ hLcP
    rwa [compl_compl] at h
  -- Hence L ∈ NP, so L is NP-complete, and an NP-complete language in P gives P = NP.
  have hLNP : L ∈ PvsNP.NP := PvsNP.Units.m2_p_subset_np hLP
  have hNPC : PvsNP.NPComplete L := ⟨hLNP, hHard⟩
  exact PvsNP.Units.m2_npc_in_p L hNPC hLP
