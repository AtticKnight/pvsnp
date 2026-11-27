import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_finite

theorem PvsNP.Units.m2_p_bounded_slice :
    ∀ (L : Language Bool) (m : ℕ),
      ({x : List Bool | x ∈ L ∧ x.length ≤ m} : Language Bool) ∈ PvsNP.P := by
  intro L m
  classical
  have key : ∀ x : List Bool,
      x ∈ ((Finset.range (m + 1)).biUnion (fun j =>
        (Finset.univ : Finset (Fin j → Bool)).image List.ofFn)).filter
          (fun x => x ∈ L) ↔ (x ∈ L ∧ x.length ≤ m) := by
    intro x
    constructor
    · intro hx
      rw [Finset.mem_filter] at hx
      refine ⟨hx.2, ?_⟩
      rw [Finset.mem_biUnion] at hx
      obtain ⟨j, hj, hxj⟩ := hx.1
      rw [Finset.mem_image] at hxj
      obtain ⟨f, _, hf⟩ := hxj
      have hlen : x.length = j := by rw [← hf, List.length_ofFn]
      rw [Finset.mem_range] at hj
      omega
    · intro hx
      rw [Finset.mem_filter]
      refine ⟨?_, hx.1⟩
      rw [Finset.mem_biUnion]
      refine ⟨x.length, Finset.mem_range.mpr (by omega), ?_⟩
      rw [Finset.mem_image]
      exact ⟨x.get, Finset.mem_univ _, List.ofFn_get x⟩
  have heq : ({x : List Bool | x ∈ L ∧ x.length ≤ m} : Language Bool) =
      ({x : List Bool | x ∈ ((Finset.range (m + 1)).biUnion (fun j =>
        (Finset.univ : Finset (Fin j → Bool)).image List.ofFn)).filter
          (fun x => x ∈ L)} : Language Bool) := by
    ext x
    simp only [Set.mem_setOf_eq]
    exact (key x).symm
  rw [heq]
  exact PvsNP.Units.m2_p_finite _
