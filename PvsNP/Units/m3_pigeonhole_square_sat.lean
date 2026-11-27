import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_pigeonhole_square_sat

theorem diag {n i j : ℕ} (hj : j < n)
    (h : i * n + j ∈ (List.range n).map (fun k => k * n + k)) : i = j := by
  obtain ⟨k, hk, e⟩ := List.mem_map.mp h
  have hk' : k < n := List.mem_range.mp hk
  have hki : k = i := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (k + 1) * n ≤ i * n := Nat.mul_le_mul_right n hlt
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    · have h1 : (i + 1) * n ≤ k * n := Nat.mul_le_mul_right n hgt
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
  rw [hki] at e
  omega

end PvsNP.Units.m3_pigeonhole_square_sat

open PvsNP.Units.m3_pigeonhole_square_sat in
theorem PvsNP.Units.m3_pigeonhole_square_sat : ∀ n : ℕ,
  SAT ((List.range n).map (fun i => (List.range n).map (fun j => (true, i * n + j))) ++
    (List.range n).flatMap (fun j =>
      ((List.range n).sublistsLen 2).map (fun p => p.map (fun i => (false, i * n + j))))) := by
  intro n
  refine ⟨(List.range n).map (fun k => k * n + k), ?_⟩
  apply (evalCnf_clause_iff _ _).mpr
  intro C hC
  rcases List.mem_append.mp hC with h1 | h1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h1
    refine (evalClause_literal_iff _ _).mpr ⟨(true, i * n + i), List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
    have hm : i * n + i ∈ (List.range n).map (fun k => k * n + k) := List.mem_map.mpr ⟨i, hi, rfl⟩
    simp only [evalLiteral, evalVar, hm, decide_true]
  · obtain ⟨j, hj, hC'⟩ := List.mem_flatMap.mp h1
    have hj' : j < n := List.mem_range.mp hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hC'
    obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp hp
    have hnd : p.Nodup := List.nodup_range.sublist hsub
    match p, hlen, hnd with
    | [i1, i2], _, hnd' =>
      have hne : i1 ≠ i2 := by
        intro e
        rw [e] at hnd'
        simp at hnd'
      by_cases h1' : i1 * n + j ∈ (List.range n).map (fun k => k * n + k)
      · have e1 := diag hj' h1'
        have h2' : i2 * n + j ∉ (List.range n).map (fun k => k * n + k) := by
          intro h2
          have e2 := diag hj' h2
          exact hne (e1.trans e2.symm)
        refine (evalClause_literal_iff _ _).mpr ⟨(false, i2 * n + j), by simp, ?_⟩
        simp only [evalLiteral, evalVar, h2', decide_false, decide_true]
      · refine (evalClause_literal_iff _ _).mpr ⟨(false, i1 * n + j), by simp, ?_⟩
        simp only [evalLiteral, evalVar, h1', decide_false, decide_true]
