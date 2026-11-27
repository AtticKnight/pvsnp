import Mathlib

import PvsNP.Defs

import CookLevin

/-- A chain of implications from a true variable to a false one is unsatisfiable.
The unit clause `[(true, 0)]` forces `0` into the assignment; each clause
`[(false, i), (true, i + 1)]` propagates membership one step forward, so `n`
is forced in as well, contradicting the unit clause `[(false, n)]`. -/
theorem PvsNP.Units.m3_implication_chain_unsat :
    ∀ n : ℕ, ¬ SAT ([(true, 0)] :: [(false, n)] ::
      (List.range n).map (fun i => [(false, i), (true, i + 1)])) := by
  intro n h
  obtain ⟨a, ha⟩ := h
  have ha2 : evalCnf a ([(true, 0)] :: [(false, n)] ::
      (List.range n).map (fun i => [(false, i), (true, i + 1)])) = true := ha
  rw [evalCnf_clause_iff] at ha2
  -- Literal evaluation, in terms of membership in the assignment.
  have litT : ∀ v : ℕ, evalLiteral a (true, v) = true ↔ v ∈ a := by
    intro v
    simp [evalLiteral, evalVar]
  have litF : ∀ v : ℕ, evalLiteral a (false, v) = true ↔ v ∉ a := by
    intro v
    simp [evalLiteral, evalVar]
  -- The three kinds of clauses are in the CNF.
  have mem0 : [(true, 0)] ∈ [(true, 0)] :: [(false, n)] ::
      (List.range n).map (fun i => [(false, i), (true, i + 1)]) := by simp
  have memn : [(false, n)] ∈ [(true, 0)] :: [(false, n)] ::
      (List.range n).map (fun i => [(false, i), (true, i + 1)]) := by simp
  have memi : ∀ i : ℕ, i < n →
      [(false, i), (true, i + 1)] ∈ [(true, 0)] :: [(false, n)] ::
        (List.range n).map (fun j => [(false, j), (true, j + 1)]) := by
    intro i hi
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  -- The unit clause [(true, 0)] forces 0 ∈ a.
  have h0 : 0 ∈ a := by
    have hc := ha2 _ mem0
    rw [evalClause_literal_iff] at hc
    obtain ⟨l, hl, hle⟩ := hc
    rw [List.mem_singleton] at hl
    subst hl
    exact (litT 0).mp hle
  -- Each link clause propagates membership one step forward.
  have hstep : ∀ i : ℕ, i < n → i ∈ a → i + 1 ∈ a := by
    intro i hi himem
    have hc := ha2 _ (memi i hi)
    rw [evalClause_literal_iff] at hc
    obtain ⟨l, hl, hle⟩ := hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact absurd himem ((litF i).mp hle)
    · exact (litT (i + 1)).mp hle
  -- Hence every i ≤ n is in a.
  have hall : ∀ i : ℕ, i ≤ n → i ∈ a := by
    intro i
    induction i with
    | zero => intro _; exact h0
    | succ i ih =>
        intro hle
        exact hstep i (Nat.lt_of_succ_le hle) (ih (Nat.le_of_succ_le hle))
  -- But the unit clause [(false, n)] forces n ∉ a: contradiction.
  have hn : n ∉ a := by
    have hc := ha2 _ memn
    rw [evalClause_literal_iff] at hc
    obtain ⟨l, hl, hle⟩ := hc
    rw [List.mem_singleton] at hl
    subst hl
    exact (litF n).mp hle
  exact hn (hall n le_rfl)
