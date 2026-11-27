import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_satstr_false_cons : ∀ x : List Bool, ¬ SATStr (false :: x) := by
  intro x ⟨a, ha⟩
  have hmem : [] ∈ SATStr.cnfOf (false :: x) := by
    rw [SATStr.cnfOf, CnfWellFormed.parseTotal]
    by_cases hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits (false :: x)) = true
    · rw [if_pos hwf]
      have hstr : CookLevin.Lang.strBits (false :: x) = 0 :: CookLevin.Lang.strBits x := rfl
      rw [hstr, CnfSerialize.decCnf, List.length_cons, CnfSerialize.decCnfAux]
      · rw [CnfSerialize.decClause, Option.bind_some]
        cases CnfSerialize.decCnfAux (CookLevin.Lang.strBits x).length (CookLevin.Lang.strBits x) with
        | none => simp
        | some N => simp
      · intro h; cases h
    · rw [if_neg hwf]
      simp
  have hclause : evalClause a [] = true := (evalCnf_clause_iff a _).mp ha [] hmem
  exact Bool.noConfusion hclause
