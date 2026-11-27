import Mathlib
import PvsNP.Defs
import CookLevin

/-- Under an assignment making a literal true, a CNF has the value of its
    simplification by that literal (drop clauses that already contain the
    literal; drop the opposite literal from the remaining clauses). -/
theorem PvsNP.Units.m3_eval_conditioning :
    ∀ (a : assgn) (N : cnf) (l : literal), evalLiteral a l = true →
      evalCnf a N =
        evalCnf a ((N.filter (fun C => decide (l ∉ C))).map
          (fun C => C.filter (fun m => decide (m ≠ (!l.1, l.2))))) := by
  intro a N l hl
  rcases l with ⟨s, v⟩
  have hsv : evalVar a v = s := by
    simpa [evalLiteral] using hl
  have hneg : evalLiteral a (!s, v) = false := by
    simp [evalLiteral, hsv]
  have hiff :
      evalCnf a N = true ↔
        evalCnf a ((N.filter (fun C => decide ((s, v) ∉ C))).map
          (fun C => C.filter (fun m => decide (m ≠ (!s, v))))) = true := by
    constructor
    · intro hN
      refine (evalCnf_clause_iff a _).mpr ?_
      intro C' hC'
      obtain ⟨C, hCfilt, rfl⟩ := List.mem_map.mp hC'
      obtain ⟨hCN, _hlC⟩ := List.mem_filter.mp hCfilt
      have hCtrue := (evalCnf_clause_iff a N).mp hN C hCN
      obtain ⟨m, hmC, hma⟩ := (evalClause_literal_iff a C).mp hCtrue
      refine (evalClause_literal_iff a _).mpr
        ⟨m, List.mem_filter.mpr ⟨hmC, decide_eq_true_eq.mpr ?_⟩, hma⟩
      intro heq
      subst heq
      rw [hneg] at hma
      exact Bool.noConfusion hma
    · intro hN'
      refine (evalCnf_clause_iff a _).mpr ?_
      intro C hC
      by_cases hlC : (s, v) ∈ C
      · exact (evalClause_literal_iff a C).mpr ⟨(s, v), hlC, hl⟩
      · have hC' :
            C.filter (fun m => decide (m ≠ (!s, v))) ∈
              (N.filter (fun C => decide ((s, v) ∉ C))).map
                (fun C => C.filter (fun m => decide (m ≠ (!s, v)))) :=
          List.mem_map.mpr ⟨C, List.mem_filter.mpr ⟨hC, decide_eq_true_eq.mpr hlC⟩, rfl⟩
        have hCtrue := (evalCnf_clause_iff a _).mp hN' _ hC'
        obtain ⟨m, hmfilt, hma⟩ := (evalClause_literal_iff a _).mp hCtrue
        obtain ⟨hmC, _⟩ := List.mem_filter.mp hmfilt
        exact (evalClause_literal_iff a C).mpr ⟨m, hmC, hma⟩
  cases hN : evalCnf a N
  · cases hN' : evalCnf a
        ((N.filter (fun C => decide ((s, v) ∉ C))).map
          (fun C => C.filter (fun m => decide (m ≠ (!s, v)))))
    · rfl
    · have hcontr := hiff.mpr hN'
      rw [hN] at hcontr
      exact Bool.noConfusion hcontr
  · cases hN' : evalCnf a
        ((N.filter (fun C => decide ((s, v) ∉ C))).map
          (fun C => C.filter (fun m => decide (m ≠ (!s, v)))))
    · have hcontr := hiff.mp hN
      rw [hN'] at hcontr
      exact Bool.noConfusion hcontr
    · rfl
