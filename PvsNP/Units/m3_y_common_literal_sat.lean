import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_y_common_literal_sat

theorem evalLiteral_common (l : literal) :
    evalLiteral (if l.1 then [l.2] else []) l = true := by
  rcases l with ⟨b, v⟩
  cases b with
  | true => simp [evalLiteral, evalVar]
  | false => simp [evalLiteral, evalVar]

end PvsNP.Units.m3_y_common_literal_sat

theorem PvsNP.Units.m3_y_common_literal_sat :
    ∀ (N : cnf) (l : literal), (∀ C ∈ N, l ∈ C) → SAT N := by
  intro N l hl
  refine ⟨if l.1 then [l.2] else [], ?_⟩
  simp only [satisfiesCnf, evalCnf_clause_iff]
  intro C hC
  simp only [evalClause_literal_iff]
  exact ⟨l, hl C hC, PvsNP.Units.m3_y_common_literal_sat.evalLiteral_common l⟩
