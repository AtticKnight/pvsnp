import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tf_fun_flatmap_all

/-- Writing the bit length of a string's length in unary takes polynomial time: turn every
bit of the input into `true` (a unary string of the input's length, `tf_fun_flatmap_all`),
then take its binary logarithm in unary (`cpt_lgU` of the settled unit `fr_ladner`;
`lgU_un` says the result is the unary string of `Nat.size` of the length). -/
theorem PvsNP.Units.m2_tm_unary_log :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (Nat.size x.length) true) := by
  have hflat : ∀ x : List Bool, x.flatMap (fun _ => [true]) = List.replicate x.length true := by
    intro x
    induction x with
    | nil => rfl
    | cons b xs ih =>
      simp only [List.flatMap_cons, List.length_cons, List.replicate_succ,
        List.cons_append, List.nil_append, ih]
  have h1 := PvsNP.Units.tf_fun_flatmap_all (fun _ => [true])
  have hfun : (fun s : List Bool =>
      PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.lgU (s.flatMap (fun _ => [true]))) =
      (fun x : List Bool => List.replicate (Nat.size x.length) true) := by
    funext s
    rw [hflat s]
    exact PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.lgU_un s.length
  rw [← hfun]
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner.cpt_lgU h1
