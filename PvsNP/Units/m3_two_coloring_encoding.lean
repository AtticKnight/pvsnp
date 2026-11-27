import Mathlib
import PvsNP.Defs
import CookLevin

/-
# Two-colouring encoding: SAT iff the graph is 2-colourable

Original proof for the make.fun desk bounty desk-pvsnp-20261127,
unit `m3_two_coloring_encoding` (weight 1).

Mathematical idea: for each edge `e`, the two clauses `x_{e.1} ∨ x_{e.2}`
and `¬x_{e.1} ∨ ¬x_{e.2}` force the endpoints to take different values.
So a satisfying assignment is exactly a 2-colouring `col := evalVar a`,
and conversely a 2-colouring gives the assignment of its true endpoints.

Adapted from the settled units `m3_xor_cycle_sat_iff` (commit e904ea7,
same two-clause "different value" shape, `mem_iff` + `evalCnf_clause_iff`
+ `evalClause_literal_iff` pattern) and `m3_coloring_encoding`
(commit 5db44f0, same colouring-encoding family). No other unit file is
imported.
-/

set_option autoImplicit false

theorem PvsNP.Units.m3_two_coloring_encoding :
    ∀ E : List (var × var),
      SAT (E.flatMap (fun e => [[(true, e.1), (true, e.2)], [(false, e.1), (false, e.2)]])) ↔
        ∃ col : var → Bool, ∀ e ∈ E, col e.1 ≠ col e.2 := by
  intro E
  -- Membership in the flatMap: a clause belongs iff it is one of the two
  -- clauses for some edge `e ∈ E`.
  have mem_iff : ∀ C : clause,
      C ∈ E.flatMap (fun e => [[(true, e.1), (true, e.2)], [(false, e.1), (false, e.2)]]) ↔
        ∃ e ∈ E, C = [(true, e.1), (true, e.2)] ∨ C = [(false, e.1), (false, e.2)] := by
    intro C
    constructor
    · intro h
      rw [List.mem_flatMap] at h
      obtain ⟨e, he, hCe⟩ := h
      exact ⟨e, he, by simpa using hCe⟩
    · rintro ⟨e, he, hC⟩
      rw [List.mem_flatMap]
      exact ⟨e, he, by simpa using hC⟩
  constructor
  · -- SAT → 2-colouring: take `col := evalVar a`.
    rintro ⟨a, ha⟩
    rw [satisfiesCnf, evalCnf_clause_iff] at ha
    refine ⟨evalVar a, fun e he => ?_⟩
    have hpos := ha _ ((mem_iff _).mpr ⟨e, he, Or.inl rfl⟩)
    have hneg := ha _ ((mem_iff _).mpr ⟨e, he, Or.inr rfl⟩)
    simp only [evalClause, List.any_cons, List.any_nil, evalLiteral, Bool.or_eq_true,
      decide_eq_true_eq] at hpos hneg
    rcases Bool.eq_false_or_eq_true (evalVar a e.1) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (evalVar a e.2) with h2 | h2 <;>
    simp_all
  · -- 2-colouring → SAT: the assignment of true-coloured endpoints.
    rintro ⟨col, hcol⟩
    set a := (E.flatMap (fun e => [e.1, e.2])).filter (fun v => col v) with ha_def
    have hmem_end : ∀ v, v ∈ E.flatMap (fun e => [e.1, e.2]) → evalVar a v = col v := by
      intro v hv
      have hiff : v ∈ a ↔ col v = true := by
        simp only [ha_def, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
      show decide (v ∈ a) = col v
      by_cases h : v ∈ a
      · rw [decide_eq_true h]; exact (hiff.mp h).symm
      · rw [decide_eq_false h]
        cases hcv : col v with
        | true => exact absurd (hiff.mpr hcv) h
        | false => rfl
    refine ⟨a, ?_⟩
    rw [satisfiesCnf, evalCnf_clause_iff]
    intro C hC
    obtain ⟨e, he, hCe⟩ := (mem_iff C).mp hC
    have hm1 : e.1 ∈ E.flatMap (fun e => [e.1, e.2]) :=
      List.mem_flatMap.mpr ⟨e, he, by simp⟩
    have hm2 : e.2 ∈ E.flatMap (fun e => [e.1, e.2]) :=
      List.mem_flatMap.mpr ⟨e, he, by simp⟩
    have hne : evalVar a e.1 ≠ evalVar a e.2 := by
      rw [hmem_end e.1 hm1, hmem_end e.2 hm2]; exact hcol e he
    have hpos : evalVar a e.1 = true ∨ evalVar a e.2 = true := by
      rcases Bool.eq_false_or_eq_true (evalVar a e.1) with h1 | h1
      · exact Or.inl h1
      · right
        rcases Bool.eq_false_or_eq_true (evalVar a e.2) with h2 | h2
        · exact h2
        · exact absurd (h1.trans h2.symm) hne
    have hneg : evalVar a e.1 = false ∨ evalVar a e.2 = false := by
      rcases Bool.eq_false_or_eq_true (evalVar a e.1) with h1 | h1
      · right
        rcases Bool.eq_false_or_eq_true (evalVar a e.2) with h2 | h2
        · exact absurd (h1.trans h2.symm) hne
        · exact h2
      · exact Or.inl h1
    rcases hCe with rfl | rfl
    · rw [evalClause_literal_iff]
      rcases hpos with h1 | h1
      · exact ⟨(true, e.1), by simp, by simp [evalLiteral, h1]⟩
      · exact ⟨(true, e.2), by simp, by simp [evalLiteral, h1]⟩
    · rw [evalClause_literal_iff]
      rcases hneg with h1 | h1
      · exact ⟨(false, e.1), by simp, by simp [evalLiteral, h1]⟩
      · exact ⟨(false, e.2), by simp, by simp [evalLiteral, h1]⟩
