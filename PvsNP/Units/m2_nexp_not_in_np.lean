import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Some NEXP language is not in NP (TM2).

The separating language is `DLang` from the settled Ladner unit
`PvsNP.Units.fr_ladner`, with its verifier `RD` and the exponential bound
`k = 2`: `DLang` is `{z | ∃ w, w.length ≤ 2 ^ (z.length ^ 2) + 2 ∧ RD (z, w) = true}`,
and `RD` is computable in polynomial time (`cpt_RD`), so `DLang` is in NEXP
in exactly the form this statement asks for. And `DLang` is not in NP
(`DLang_not_NP`), carried over to the campaign's `NP` by the bridge `NP_iff`.
-/

namespace PvsNP.Units.m2_nexp_not_in_np

/-- `RD` is computable in polynomial time in the campaign's sense. -/
theorem poly_RD : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.RD :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_RD

/-- Membership in `DLang` is exactly the exponential-bound verifier condition. -/
theorem mem_DLang (x : List Bool) :
    x ∈ PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.DLang ↔
      ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ 2) + 2 ∧
        PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.RD (x, w) = true :=
  Iff.rfl

/-- `DLang` is not in the campaign's `NP`. -/
theorem DLang_not_NP :
    PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.DLang ∉ PvsNP.NP := by
  intro h
  exact PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.DLang_not_NP
    ((PvsNP.Units.fr_ladner.NP_iff _).1 h)

end PvsNP.Units.m2_nexp_not_in_np

theorem PvsNP.Units.m2_nexp_not_in_np :
    ∃ L : Language Bool,
      (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) ∧
      L ∉ PvsNP.NP :=
  Exists.intro PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.DLang
    (And.intro
      (Exists.intro PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.RD
        (Exists.intro 2
          (And.intro PvsNP.Units.m2_nexp_not_in_np.poly_RD
            (fun x => PvsNP.Units.m2_nexp_not_in_np.mem_DLang x))))
      PvsNP.Units.m2_nexp_not_in_np.DLang_not_NP)
