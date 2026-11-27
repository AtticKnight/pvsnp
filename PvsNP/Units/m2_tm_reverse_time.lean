import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_reverse_polytime

/-
Reversing a string takes at most `n + 1` steps.

The machine is the one of the settled unit `PvsNP.Units.m2_reverse_polytime` (imported, not
copied): `revTM` pops the input stack onto the output stack, one step a symbol and one to halt,
and `rev_outputs` is its run within `(X + C 1).eval n` steps. Read as a timed machine by Mathlib's
`Turing.TM2ComputableInPolyTime.toTM2ComputableInTime`, its time at `n` is `n + 1`.
-/

namespace PvsNP.Units.m2_tm_reverse_time

/-- The reversal machine of `PvsNP.Units.m2_reverse_polytime`, with its polynomial time bound. -/
noncomputable def revPoly : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => x.reverse) :=
  { tm := PvsNP.Units.m2_reverse_polytime.revTM
    inputAlphabet := PvsNP.Units.m2_reverse_polytime.inEquiv
    outputAlphabet := PvsNP.Units.m2_reverse_polytime.outEquiv
    time := Polynomial.X + Polynomial.C 1
    outputsFun := PvsNP.Units.m2_reverse_polytime.rev_outputs }

end PvsNP.Units.m2_tm_reverse_time

theorem PvsNP.Units.m2_tm_reverse_time :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => x.reverse),
      ∀ n : ℕ, M.time n ≤ n + 1 := by
  refine ⟨PvsNP.Units.m2_tm_reverse_time.revPoly.toTM2ComputableInTime, fun n => ?_⟩
  change (Polynomial.X + Polynomial.C 1 : Polynomial ℕ).eval n ≤ n + 1
  simp
