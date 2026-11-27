import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_np_projection
import PvsNP.Units.fr_ladner

/-- NP is closed under short extensions: the prefixes of NP strings with a short
    completion. This is the settled projection unit `m2_np_projection` with
    `g (x, c) = x ++ c` (polytime by `cpt_append` of the settled unit `fr_ladner`)
    and the bound `p = X`. -/
theorem PvsNP.Units.m2_np_prefix_closed :
    ∀ L ∈ PvsNP.NP,
      ({x : List Bool | ∃ y : List Bool, y.length ≤ x.length ∧ x ++ y ∈ L} :
        Language Bool) ∈ PvsNP.NP := by
  intro L hL
  have hg : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1 ++ p.2) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_append
  have h := PvsNP.Units.m2_np_projection L
    (fun p : List Bool × List Bool => p.1 ++ p.2) Polynomial.X hL hg
  simpa only [Polynomial.eval_X] using h
