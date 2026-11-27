import Mathlib
import PvsNP.Defs
import CookLevin

/-- Well-formed CNF encodings are closed under concatenation: if `strBits x` and
    `strBits y` are both well-formed, so is `strBits (x ++ y)`. On a well-formed
    string the decode is exact, so each side is an encoding of some CNF; the
    encoding takes `++` to `++`, and `strBits` is a `map`, hence the concatenation
    is the encoding of the concatenated CNFs, which is well-formed. -/
theorem PvsNP.Units.m3_wf_append : ∀ x y : List Bool, CnfWellFormed.wfCnfB (CookLevin.Lang.strBits x) = true →
  CnfWellFormed.wfCnfB (CookLevin.Lang.strBits y) = true →
    CnfWellFormed.wfCnfB (CookLevin.Lang.strBits (x ++ y)) = true := by
  intro x y hx hy
  obtain ⟨N, hN⟩ := (CnfWellFormed.wfCnfB_iff _ (CookLevin.Lang.strBits_bit x)).mp hx
  obtain ⟨M, hM⟩ := (CnfWellFormed.wfCnfB_iff _ (CookLevin.Lang.strBits_bit y)).mp hy
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
  have hmap : CookLevin.Lang.strBits (x ++ y)
      = CookLevin.Lang.strBits x ++ CookLevin.Lang.strBits y := by
    simp only [CookLevin.Lang.strBits, List.map_append]
  rw [hmap, ← hN, ← hM, ← happ]
  exact CnfWellFormed.wfCnfB_encodeCnf _
