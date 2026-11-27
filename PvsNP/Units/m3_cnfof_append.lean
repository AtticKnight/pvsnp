import Mathlib
import PvsNP.Defs
import CookLevin

/-- Decoding the concatenation of two well-formed encoded CNFs gives the concatenated CNF.
    On a well-formed string the decode is exact (`CnfWellFormed.encodeCnf_parseTotal`), so
    `strBits x = encodeCnf (cnfOf x)` and `strBits y = encodeCnf (cnfOf y)`. The encoding
    `EvalCnfCmd.encodeCnf` is a `foldr` of clause encodings and so takes `++` to `++`,
    `CookLevin.Lang.strBits` is a `map`, hence `strBits (x ++ y) = encodeCnf (cnfOf x ++ cnfOf y)`,
    and `CnfWellFormed.parseTotal_encodeCnf` reads that encoding back. -/
theorem PvsNP.Units.m3_cnfof_append : ∀ x y : List Bool, CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true →
  CnfWellFormed.wfCnfB (CookLevin.Lang.strBits y) = true →
    SATStr.cnfOf (x ++ y) = SATStr.cnfOf x ++ SATStr.cnfOf y := by
  intro x y hx hy
  have happ : ∀ N M : cnf, EvalCnfCmd.encodeCnf (N ++ M)
      = EvalCnfCmd.encodeCnf N ++ EvalCnfCmd.encodeCnf M := by
    intro N M
    induction N with
    | nil => rfl
    | cons C N ih =>
      show EvalCnfCmd.encodeClause C ++ EvalCnfCmd.encodeCnf (N ++ M)
        = (EvalCnfCmd.encodeClause C ++ EvalCnfCmd.encodeCnf N) ++ EvalCnfCmd.encodeCnf M
      rw [ih]
      exact (List.append_assoc _ _ _).symm
  have ex : EvalCnfCmd.encodeCnf (SATStr.cnfOf x) = CookLevin.Lang.strBits x :=
    CnfWellFormed.encodeCnf_parseTotal _ (CookLevin.Lang.strBits_bit x) hx
  have ey : EvalCnfCmd.encodeCnf (SATStr.cnfOf y) = CookLevin.Lang.strBits y :=
    CnfWellFormed.encodeCnf_parseTotal _ (CookLevin.Lang.strBits_bit y) hy
  have hmap : CookLevin.Lang.strBits (x ++ y)
      = CookLevin.Lang.strBits x ++ CookLevin.Lang.strBits y := by
    simp only [CookLevin.Lang.strBits, List.map_append]
  have hbits : CookLevin.Lang.strBits (x ++ y)
      = EvalCnfCmd.encodeCnf (SATStr.cnfOf x ++ SATStr.cnfOf y) := by
    rw [happ, ex, ey, hmap]
  exact (congrArg CnfWellFormed.parseTotal hbits).trans
    (CnfWellFormed.parseTotal_encodeCnf (SATStr.cnfOf x ++ SATStr.cnfOf y))
