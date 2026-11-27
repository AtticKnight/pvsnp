import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_satstr_constant

/-- A string of n zero bits decodes to exactly n empty clauses: the bits of
    `List.replicate n false` are `List.replicate n 0`, which is precisely the
    encoding of `List.replicate n []` (the settled unit `m3_satstr_constant`
    computes that encoding), and `CnfWellFormed.parseTotal_encodeCnf` reads
    the encoding straight back. -/
theorem PvsNP.Units.m3_cnfof_all_false :
    ∀ n : ℕ, SATStr.cnfOf (List.replicate n false) = List.replicate n [] := by
  intro n
  have hbits : CookLevin.Lang.strBits (List.replicate n false)
      = List.replicate n 0 := by
    simp [CookLevin.Lang.strBits]
  show CnfWellFormed.parseTotal (CookLevin.Lang.strBits (List.replicate n false)) = _
  rw [hbits, ← PvsNP.Units.m3_satstr_constant.encodeCnf_replicate_empty n,
    CnfWellFormed.parseTotal_encodeCnf]
