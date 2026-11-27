import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_all_negative_units :
    ∀ (a : assgn) (vs : List var), satisfiesCnf a (vs.map (fun v => [(false, v)])) ↔ ∀ v ∈ vs, v ∉ a := by
  intro a vs
  simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, evalVar]
