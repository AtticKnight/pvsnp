import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_satstr_wellformed :
    ∀ x : List Bool, SATStr x → CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true := by
  intro x hSAT
  by_cases hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true
  · exact hwf
  · have hb : SATStr.cnfOf x = CnfWellFormed.botCnf :=
      CnfWellFormed.parseTotal_of_not_wf _ (by simpa using hwf)
    exact absurd (hb ▸ hSAT) CnfWellFormed.not_sat_botCnf
