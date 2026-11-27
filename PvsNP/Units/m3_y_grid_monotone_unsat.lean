import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_y_grid_monotone_unsat :
    ∀ m n : ℕ,
      ¬ SAT ([(true, 0)] :: [(false, m * (n + 1) + n)] ::
        ((List.range m).flatMap (fun i => (List.range (n + 1)).map (fun j =>
            [(false, i * (n + 1) + j), (true, (i + 1) * (n + 1) + j)])) ++
          (List.range (m + 1)).flatMap (fun i => (List.range n).map (fun j =>
            [(false, i * (n + 1) + j), (true, i * (n + 1) + j + 1)])))) := by
  intro m n ⟨a, ha⟩
  have hall := (evalCnf_clause_iff a _).mp ha
  have h0 : evalVar a 0 = true := by
    have hc := hall [(true, 0)] (by simp)
    obtain ⟨l, hl, hlit⟩ := (evalClause_literal_iff a _).mp hc
    simp only [List.mem_singleton] at hl
    subst hl
    simpa [evalLiteral] using hlit
  have hlast : evalVar a (m * (n + 1) + n) = false := by
    have hc := hall [(false, m * (n + 1) + n)] (by simp)
    obtain ⟨l, hl, hlit⟩ := (evalClause_literal_iff a _).mp hc
    simp only [List.mem_singleton] at hl
    subst hl
    simpa [evalLiteral] using hlit
  have hdown : ∀ i < m, ∀ j < n + 1,
      evalVar a (i * (n + 1) + j) = true → evalVar a ((i + 1) * (n + 1) + j) = true := by
    intro i hi j hj hcur
    have hmem : [(false, i * (n + 1) + j), (true, (i + 1) * (n + 1) + j)] ∈
        ([(true, 0)] :: [(false, m * (n + 1) + n)] ::
          ((List.range m).flatMap (fun i => (List.range (n + 1)).map (fun j =>
              [(false, i * (n + 1) + j), (true, (i + 1) * (n + 1) + j)])) ++
            (List.range (m + 1)).flatMap (fun i => (List.range n).map (fun j =>
              [(false, i * (n + 1) + j), (true, i * (n + 1) + j + 1)])))) := by
      refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
      rw [List.mem_flatMap]
      exact ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩
    have hc := hall _ hmem
    obtain ⟨l, hl, hlit⟩ := (evalClause_literal_iff a _).mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simp [evalLiteral, hcur] at hlit
    · simpa [evalLiteral] using hlit
  have hright : ∀ i < m + 1, ∀ j < n,
      evalVar a (i * (n + 1) + j) = true → evalVar a (i * (n + 1) + j + 1) = true := by
    intro i hi j hj hcur
    have hmem : [(false, i * (n + 1) + j), (true, i * (n + 1) + j + 1)] ∈
        ([(true, 0)] :: [(false, m * (n + 1) + n)] ::
          ((List.range m).flatMap (fun i => (List.range (n + 1)).map (fun j =>
              [(false, i * (n + 1) + j), (true, (i + 1) * (n + 1) + j)])) ++
            (List.range (m + 1)).flatMap (fun i => (List.range n).map (fun j =>
              [(false, i * (n + 1) + j), (true, i * (n + 1) + j + 1)])))) := by
      refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ ?_))
      rw [List.mem_flatMap]
      exact ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩
    have hc := hall _ hmem
    obtain ⟨l, hl, hlit⟩ := (evalClause_literal_iff a _).mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simp [evalLiteral, hcur] at hlit
    · simpa [evalLiteral] using hlit
  have hcol : ∀ i ≤ m, evalVar a (i * (n + 1) + 0) = true := by
    intro i
    induction i with
    | zero => intro _; simpa using h0
    | succ i ih =>
      intro hi
      exact hdown i (by omega) 0 (Nat.zero_lt_succ n) (ih (by omega))
  have hrow : ∀ j ≤ n, evalVar a (m * (n + 1) + j) = true := by
    intro j
    induction j with
    | zero => intro _; exact hcol m le_rfl
    | succ j ih =>
      intro hj
      exact hright m (Nat.lt_succ_self m) j (by omega) (ih (by omega))
  have hfin := hrow n le_rfl
  rw [hlast] at hfin
  exact Bool.false_ne_true hfin
