import Mathlib
import PvsNP.Defs
import CookLevin

/-- Canonical CNF serialization gives existence, and the bit decoder gives uniqueness. -/
theorem PvsNP.Units.m3_cnfof_bijective :
    ∀ N : cnf, ∃! x : List Bool,
      CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true ∧ SATStr.cnfOf x = N := by
  intro N
  let x := CookLevin.Lang.boolsOf (EvalCnfCmd.encodeCnf N)
  have hx : CookLevin.Lang.strBits x = EvalCnfCmd.encodeCnf N :=
    CookLevin.Lang.strBits_boolsOf (EvalCnfCmd.encodeCnf_bit N)
  refine ⟨x, ?_, ?_⟩
  · constructor
    · rw [hx]
      exact CnfWellFormed.wfCnfB_encodeCnf N
    · change CnfWellFormed.parseTotal (CookLevin.Lang.strBits x) = N
      rw [hx, CnfWellFormed.parseTotal_encodeCnf]
  · intro y hy
    have he := CnfWellFormed.encodeCnf_parseTotal
      (CookLevin.Lang.strBits y) (CookLevin.Lang.strBits_bit y) hy.1
    change EvalCnfCmd.encodeCnf (SATStr.cnfOf y) = CookLevin.Lang.strBits y at he
    rw [hy.2] at he
    have hs : CookLevin.Lang.strBits y = CookLevin.Lang.strBits x :=
      he.symm.trans hx.symm
    apply Option.some.inj
    simpa only [CookLevin.Lang.decBits_strBits] using
      congrArg CookLevin.Lang.decBits hs
