import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_cnfof_length_exact

theorem encodeLit_len (l : literal) : (EvalCnfCmd.encodeLit l).length = l.2 + 3 := by
  rcases l with ⟨pol, v⟩
  show (1 :: (if pol then 1 else 0) :: (List.replicate v 1 ++ [0])).length = v + 3
  simp

def cBody (C : clause) : List Nat :=
  C.foldr (fun m acc => EvalCnfCmd.encodeLit m ++ acc) []

theorem cBody_len_exact (C : clause) :
    (cBody C).length = (C.map (fun l => l.2 + 3)).sum := by
  induction C with
  | nil => rfl
  | cons hd tl ih =>
    show (EvalCnfCmd.encodeLit hd ++ cBody tl).length = (hd.2 + 3) + (tl.map (fun l => l.2 + 3)).sum
    rw [List.length_append, encodeLit_len, ih]

theorem encodeClause_len_exact (C : clause) :
    (EvalCnfCmd.encodeClause C).length = (C.map (fun l => l.2 + 3)).sum + 1 := by
  show (cBody C ++ [0]).length = (C.map (fun l => l.2 + 3)).sum + 1
  rw [List.length_append, cBody_len_exact]
  rfl

theorem encodeCnf_len_exact (N : cnf) :
    (EvalCnfCmd.encodeCnf N).length =
      (N.map (fun C => (C.map (fun l => l.2 + 3)).sum + 1)).sum := by
  induction N with
  | nil => rfl
  | cons C tl ih =>
    show (EvalCnfCmd.encodeClause C ++ EvalCnfCmd.encodeCnf tl).length =
      ((C.map (fun l => l.2 + 3)).sum + 1) +
        (tl.map (fun C => (C.map (fun l => l.2 + 3)).sum + 1)).sum
    rw [List.length_append, encodeClause_len_exact, ih]

end PvsNP.Units.m3_cnfof_length_exact

theorem PvsNP.Units.m3_cnfof_length_exact :
    ∀ x : List Bool, CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true →
      x.length = ((SATStr.cnfOf x).map (fun C => (C.map (fun l => l.2 + 3)).sum + 1)).sum := by
  intro x hwf
  have hex : EvalCnfCmd.encodeCnf (SATStr.cnfOf x) = CookLevin.Lang.strBits x :=
    CnfWellFormed.encodeCnf_parseTotal (CookLevin.Lang.strBits x) (CookLevin.Lang.strBits_bit x) hwf
  have hlen : (EvalCnfCmd.encodeCnf (SATStr.cnfOf x)).length = x.length := by
    rw [hex, CookLevin.Lang.strBits_length]
  rw [← hlen]
  exact PvsNP.Units.m3_cnfof_length_exact.encodeCnf_len_exact (SATStr.cnfOf x)
