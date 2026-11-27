import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_cnfof_size

theorem encodeLit_len (l : literal) : (EvalCnfCmd.encodeLit l).length = l.2 + 3 := by
  rcases l with ⟨pol, v⟩
  show (1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0])).length = v + 3
  simp

def cBody (C : clause) : List Nat :=
  C.foldr (fun m acc => EvalCnfCmd.encodeLit m ++ acc) []

theorem cBody_nil : (cBody []).length = 0 := rfl

theorem cBody_cons (hd : literal) (tl : clause) :
    (cBody (hd :: tl)).length = hd.2 + 3 + (cBody tl).length := by
  show (EvalCnfCmd.encodeLit hd ++ cBody tl).length = hd.2 + 3 + (cBody tl).length
  rw [List.length_append, encodeLit_len]

theorem cBody_sum (C : clause) : 3 * C.length ≤ (cBody C).length := by
  induction C with
  | nil => simp [cBody_nil]
  | cons hd tl ih =>
    rw [cBody_cons, List.length_cons]
    omega

theorem cBody_mem (C : clause) : ∀ l ∈ C, l.2 + 3 ≤ (cBody C).length := by
  induction C with
  | nil =>
    intro l hl
    cases hl
  | cons hd tl ih =>
    intro l hl
    rw [cBody_cons]
    rcases List.mem_cons.mp hl with rfl | htl
    · exact Nat.le_add_right (l.2 + 3) (cBody tl).length
    · exact Nat.le_trans (ih l htl) (Nat.le_add_left (cBody tl).length (hd.2 + 3))

theorem encodeClause_len_eq (C : clause) :
    (EvalCnfCmd.encodeClause C).length = (cBody C).length + 1 := by
  show (cBody C ++ [0]).length = (cBody C).length + 1
  simp

theorem encodeCnf_cons_len (C : clause) (tl : cnf) :
    (EvalCnfCmd.encodeCnf (C :: tl)).length =
      (EvalCnfCmd.encodeClause C).length + (EvalCnfCmd.encodeCnf tl).length := by
  show (EvalCnfCmd.encodeClause C ++ EvalCnfCmd.encodeCnf tl).length = _
  simp

theorem encodeCnf_sum (N : cnf) :
    (N.map (fun C => 3 * C.length + 1)).sum ≤ (EvalCnfCmd.encodeCnf N).length := by
  induction N with
  | nil => simp [EvalCnfCmd.encodeCnf]
  | cons C tl ih =>
    rw [encodeCnf_cons_len, encodeClause_len_eq, List.map_cons, List.sum_cons]
    have hC := cBody_sum C
    omega

theorem encodeCnf_mem (N : cnf) :
    ∀ C ∈ N, ∀ l ∈ C, l.2 + 3 ≤ (EvalCnfCmd.encodeCnf N).length := by
  induction N with
  | nil =>
    intro C hC
    cases hC
  | cons C tl ih =>
    intro D hD l hl
    rw [encodeCnf_cons_len]
    rcases List.mem_cons.mp hD with rfl | htl
    · have h1 : l.2 + 3 ≤ (EvalCnfCmd.encodeClause D).length := by
        rw [encodeClause_len_eq]
        exact Nat.le_trans (cBody_mem D l hl) (Nat.le_succ _)
      exact Nat.le_trans h1 (Nat.le_add_right _ _)
    · exact Nat.le_trans (ih D htl l hl) (Nat.le_add_left _ _)

end PvsNP.Units.m3_cnfof_size

theorem PvsNP.Units.m3_cnfof_size :
  ∀ x : List Bool,
  ((SATStr.cnfOf x).map (fun C => 3 * C.length + 1)).sum ≤ x.length ∧
    ∀ C ∈ SATStr.cnfOf x, ∀ l ∈ C, l.2 + 3 ≤ x.length := by
  intro x
  cases hwf : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x)
  · have hbot : SATStr.cnfOf x = CnfWellFormed.botCnf :=
      CnfWellFormed.parseTotal_of_not_wf (CookLevin.Lang.strBits x) hwf
    rw [hbot]
    cases x with
    | nil =>
      have htrue : CnfWellFormed.wfCnfB (CookLevin.Lang.strBits []) = true := rfl
      rw [htrue] at hwf
      exact Bool.noConfusion hwf
    | cons b xs =>
      simp [CnfWellFormed.botCnf]
  · have hex : EvalCnfCmd.encodeCnf (SATStr.cnfOf x) = CookLevin.Lang.strBits x :=
      CnfWellFormed.encodeCnf_parseTotal (CookLevin.Lang.strBits x) (CookLevin.Lang.strBits_bit x) hwf
    have hlen : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length = x.length := by
      rw [hex, CookLevin.Lang.strBits_length]
    refine ⟨?_, ?_⟩
    · rw [← hlen]
      exact PvsNP.Units.m3_cnfof_size.encodeCnf_sum (SATStr.cnfOf x)
    · intro C hC l hl
      rw [← hlen]
      exact PvsNP.Units.m3_cnfof_size.encodeCnf_mem (SATStr.cnfOf x) C hC l hl
