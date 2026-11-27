import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_satstr_constant

theorem encodeCnf_replicate_empty (n : ℕ) :
    EvalCnfCmd.encodeCnf (List.replicate n ([] : clause)) = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, CnfSerialize.encodeCnf_cons, List.replicate_succ, ih]
    rfl

theorem wfCnfB_replicate_one_succ (m : ℕ) :
    CnfWellFormed.wfCnfB (List.replicate (m + 1) 1) = false := by
  cases m with
  | zero => rfl
  | succ k =>
    have hrun : CnfWellFormed.scanRun (List.replicate (k + 2) 1) = (true, true, 0) := by
      unfold CnfWellFormed.scanRun
      rw [List.replicate_succ, List.foldl_cons]
      have h1 : CnfWellFormed.scanStep (false, false, 0) 1 = (true, false, 0) := rfl
      rw [h1, List.replicate_succ, List.foldl_cons]
      have h2 : CnfWellFormed.scanStep (true, false, 0) 1 = (true, true, 0) := rfl
      rw [h2]
      exact CnfWellFormed.scan_replicate_one k 0
    simp [CnfWellFormed.wfCnfB, hrun]

theorem satstr_constant_aux (b : Bool) (n : ℕ) :
    SATStr (List.replicate n b) ↔ n = 0 := by
  constructor
  · intro h
    cases n with
    | zero => rfl
    | succ m =>
      exfalso
      obtain ⟨N, hN, hsat⟩ := (SATStr.satStr_iff _).mp h
      cases b with
      | false =>
        have hbits : CookLevin.Lang.strBits (List.replicate (m + 1) false) =
            List.replicate (m + 1) 0 := by
          simp [CookLevin.Lang.strBits]
        rw [hbits, ← encodeCnf_replicate_empty (m + 1)] at hN
        have hNeq : N = List.replicate (m + 1) ([] : clause) := by
          have hparse := congrArg CnfWellFormed.parseTotal hN
          rw [CnfWellFormed.parseTotal_encodeCnf, CnfWellFormed.parseTotal_encodeCnf] at hparse
          exact hparse.symm
        subst hNeq
        obtain ⟨a, ha⟩ := hsat
        rw [List.replicate_succ] at ha
        simp [satisfiesCnf, evalCnf, evalClause] at ha
      | true =>
        have hbits : CookLevin.Lang.strBits (List.replicate (m + 1) true) =
            List.replicate (m + 1) 1 := by
          simp [CookLevin.Lang.strBits]
        rw [hbits] at hN
        have hwf : CnfWellFormed.wfCnfB (List.replicate (m + 1) 1) = true := by
          rw [hN]
          exact CnfWellFormed.wfCnfB_encodeCnf N
        rw [wfCnfB_replicate_one_succ m] at hwf
        exact Bool.false_ne_true hwf
  · rintro rfl
    exact SATStr.satStr_nil

end PvsNP.Units.m3_satstr_constant

/-- A constant bit string is in SATStr only when it is empty (vendored model). -/
theorem PvsNP.Units.m3_satstr_constant :
    ∀ (b : Bool) (n : ℕ), SATStr (List.replicate n b) ↔ n = 0 :=
  PvsNP.Units.m3_satstr_constant.satstr_constant_aux
