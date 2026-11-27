import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_3sat_in_np

open CookLevin.Lang

/-!
# 3SAT reduces to SAT in polynomial time (vendored model)

The language of bit-strings encoding a satisfiable CNF with at most 3 literals
per clause is in NP by the settled unit `m3_3sat_in_np`. Since `SATStr` is NP-hard
in the vendored Cook–Levin model (`CookLevin.SATStr_NPhard`), every NP language —
in particular this one — reduces to `SATStr` in polynomial time.
-/

set_option autoImplicit false

/-- 3SAT reduces to SAT in polynomial time in the vendored Cook–Levin model. -/
theorem PvsNP.Units.m3_3sat_to_sat :
    CookLevin.reducesPoly
      (fun x => (∀ C ∈ SATStr.cnfOf x, C.length ≤ 3) ∧ SAT (SATStr.cnfOf x)) SATStr :=
  CookLevin.SATStr_NPhard _ PvsNP.Units.m3_3sat_in_np
