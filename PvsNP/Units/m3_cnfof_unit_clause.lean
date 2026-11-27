import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_cnfof_unit_clause :
    ∀ (s : Bool) (v : var),
      SATStr.cnfOf (true :: s :: List.replicate v true ++ [false, false]) = [[(s, v)]] := by
  intro s v
  have _hc := Classical.em True
  have hbits : CookLevin.Lang.strBits (true :: s :: List.replicate v true ++ [false, false]) =
      EvalCnfCmd.encodeCnf [[(s, v)]] := by
    cases s <;> simp [CookLevin.Lang.strBits, EvalCnfCmd.encodeCnf, EvalCnfCmd.encodeClause,
      EvalCnfCmd.encodeLit]
  rw [SATStr.cnfOf, hbits, CnfWellFormed.parseTotal_encodeCnf]
