import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_y_sat_single_clause

/-- A nonempty clause is satisfied by the assignment that sets the variable of one of its
literals according to the literal's polarity. -/
theorem sat_single_clause_of_ne_nil (C : clause) (hC : C ≠ []) : SAT [C] := by
  rcases C with _ | ⟨l, C⟩
  · exact absurd rfl hC
  · obtain ⟨s, v⟩ := l
    refine ⟨if s then [v] else [], (evalCnf_clause_iff _ _).mpr ?_⟩
    intro D hD
    have hD' : D = (s, v) :: C := List.mem_singleton.mp hD
    subst hD'
    rw [evalClause_literal_iff]
    refine ⟨(s, v), List.mem_cons_self, ?_⟩
    cases s <;> simp [evalLiteral, evalVar]

/-- The empty clause is never satisfied, so a satisfiable singleton CNF has a nonempty clause. -/
theorem ne_nil_of_sat_single_clause (C : clause) (h : SAT [C]) : C ≠ [] := by
  rintro rfl
  obtain ⟨a, ha⟩ := h
  have hclause : evalClause a [] = true :=
    (evalCnf_clause_iff a [[]]).mp ha [] (List.mem_singleton_self [])
  have hempty : evalClause a [] = false := rfl
  rw [hempty] at hclause
  exact Bool.noConfusion hclause

end PvsNP.Units.m3_y_sat_single_clause

theorem PvsNP.Units.m3_y_sat_single_clause :
    ∀ C : clause, SAT [C] ↔ C ≠ [] := by
  intro C
  exact ⟨PvsNP.Units.m3_y_sat_single_clause.ne_nil_of_sat_single_clause C,
    PvsNP.Units.m3_y_sat_single_clause.sat_single_clause_of_ne_nil C⟩
