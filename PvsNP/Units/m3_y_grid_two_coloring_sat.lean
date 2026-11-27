import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_grid_two_coloring_sat

private def gridAssgn (m n : ℕ) : assgn :=
  (List.range ((m + 1) * (n + 1))).filter (fun v => decide ((v / (n + 1) + v % (n + 1)) % 2 = 0))

private theorem mem_gridAssgn_iff (m n i j : ℕ) (hi : i < m + 1) (hj : j < n + 1) :
    i * (n + 1) + j ∈ gridAssgn m n ↔ (i + j) % 2 = 0 := by
  have hlt : i * (n + 1) + j < (m + 1) * (n + 1) := by
    have h1 : i * (n + 1) ≤ m * (n + 1) := Nat.mul_le_mul_right (n + 1) (by omega)
    have h2 : (m + 1) * (n + 1) = m * (n + 1) + (n + 1) := by ring
    omega
  have hdiv : (i * (n + 1) + j) / (n + 1) = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos n), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i * (n + 1) + j) % (n + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp [gridAssgn, hlt, hdiv, hmod]

private theorem eval_edge_clauses (a : assgn) (u w p : ℕ)
    (hu : u ∈ a ↔ p % 2 = 0) (hw : w ∈ a ↔ (p + 1) % 2 = 0) :
    evalClause a [(true, u), (true, w)] = true ∧
      evalClause a [(false, u), (false, w)] = true := by
  simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    evalLiteral, evalVar, decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases hp : p % 2 = 0
  · have hu' : u ∈ a := hu.mpr hp
    have hw' : w ∉ a := fun h => by have := hw.mp h; omega
    exact ⟨Or.inl hu', Or.inr hw'⟩
  · have hu' : u ∉ a := fun h => hp (hu.mp h)
    have hw' : w ∈ a := hw.mpr (by omega)
    exact ⟨Or.inr hw', Or.inl hu'⟩

theorem main : ∀ m n : ℕ,
    SAT ((List.range m).flatMap (fun i => (List.range (n + 1)).flatMap (fun j =>
        [[(true, i * (n + 1) + j), (true, (i + 1) * (n + 1) + j)],
          [(false, i * (n + 1) + j), (false, (i + 1) * (n + 1) + j)]])) ++
      (List.range (m + 1)).flatMap (fun i => (List.range n).flatMap (fun j =>
        [[(true, i * (n + 1) + j), (true, i * (n + 1) + j + 1)],
          [(false, i * (n + 1) + j), (false, i * (n + 1) + j + 1)]]))) := by
  intro m n
  refine ⟨gridAssgn m n, ?_⟩
  rw [satisfiesCnf, evalCnf_clause_iff]
  intro C hC
  rw [List.mem_append] at hC
  rcases hC with hV | hH
  · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hV
    rcases hV with ⟨i, hi, j, hj, rfl | rfl⟩
    · exact (eval_edge_clauses (gridAssgn m n) (i * (n + 1) + j) ((i + 1) * (n + 1) + j) (i + j)
        (mem_gridAssgn_iff m n i j (by omega) hj)
        (by
          have h := mem_gridAssgn_iff m n (i + 1) j (by omega) hj
          rwa [show i + 1 + j = i + j + 1 by omega] at h)).1
    · exact (eval_edge_clauses (gridAssgn m n) (i * (n + 1) + j) ((i + 1) * (n + 1) + j) (i + j)
        (mem_gridAssgn_iff m n i j (by omega) hj)
        (by
          have h := mem_gridAssgn_iff m n (i + 1) j (by omega) hj
          rwa [show i + 1 + j = i + j + 1 by omega] at h)).2
  · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hH
    rcases hH with ⟨i, hi, j, hj, rfl | rfl⟩
    · exact (eval_edge_clauses (gridAssgn m n) (i * (n + 1) + j) (i * (n + 1) + j + 1) (i + j)
        (mem_gridAssgn_iff m n i j hi (by omega))
        (by
          have h := mem_gridAssgn_iff m n i (j + 1) hi (by omega)
          rwa [show i * (n + 1) + (j + 1) = i * (n + 1) + j + 1 by omega,
               show i + (j + 1) = i + j + 1 by omega] at h)).1
    · exact (eval_edge_clauses (gridAssgn m n) (i * (n + 1) + j) (i * (n + 1) + j + 1) (i + j)
        (mem_gridAssgn_iff m n i j hi (by omega))
        (by
          have h := mem_gridAssgn_iff m n i (j + 1) hi (by omega)
          rwa [show i * (n + 1) + (j + 1) = i * (n + 1) + j + 1 by omega,
               show i + (j + 1) = i + j + 1 by omega] at h)).2

end PvsNP.Units.m3_y_grid_two_coloring_sat

theorem PvsNP.Units.m3_y_grid_two_coloring_sat :
    ∀ m n : ℕ,
      SAT ((List.range m).flatMap (fun i => (List.range (n + 1)).flatMap (fun j =>
          [[(true, i * (n + 1) + j), (true, (i + 1) * (n + 1) + j)],
            [(false, i * (n + 1) + j), (false, (i + 1) * (n + 1) + j)]])) ++
        (List.range (m + 1)).flatMap (fun i => (List.range n).flatMap (fun j =>
          [[(true, i * (n + 1) + j), (true, i * (n + 1) + j + 1)],
            [(false, i * (n + 1) + j), (false, i * (n + 1) + j + 1)]]))) :=
  PvsNP.Units.m3_y_grid_two_coloring_sat.main
