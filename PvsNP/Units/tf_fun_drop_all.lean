import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

set_option autoImplicit false

/-
Uses the settled unit `fr_ladner`'s machines (`cpt_id`, `cpt_tail1`), adapted from
github.com/brilliant-hq/pequalnp-proofs (Apache License, Version 2.0).
-/

namespace PvsNP.Units.tf_fun_drop_all

open PvsNP.Units.fr_ladner.PEqualNP.Library in
theorem drop_cpt (k : ℕ) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x.drop k) := by
  induction k with
  | zero =>
    simpa using PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
  | succ n ih =>
    have h := PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_tail1 ih
    have heq : (fun y : List Bool => (y.drop n).tail) = (fun x : List Bool => x.drop (n + 1)) := by
      funext y
      exact List.tail_drop
    rwa [heq] at h

end PvsNP.Units.tf_fun_drop_all

/-- Dropping any fixed number `k` of leading bits takes polynomial time (TM2):
    apply `cpt_tail1` from `fr_ladner` `k` times. -/
theorem PvsNP.Units.tf_fun_drop_all :
    ∀ k : ℕ, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.drop k) := by
  intro k
  exact PvsNP.Units.tf_fun_drop_all.drop_cpt k
