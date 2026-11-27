import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_polytime_comp

set_option autoImplicit false

open Turing
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

namespace PvsNP.Units.m2_tm_empty_test

/-- The two-state transducer for testing emptiness: state `false` has seen no bit yet,
state `true` has seen at least one bit. It writes nothing while reading, and at the end
emits `true` iff no bit was ever seen. -/
def emptyD : Bool → Bool → Bool × Option Bool × Option Bool
  | _, _ => (true, none, none)

/-- Final output: `true` if the input was empty, `false` otherwise. -/
def emptyFin : Bool → Option Bool
  | false => some true
  | true => some false

/-- The transducer's run: the output is `[decide (x = []) && !q]` — empty input emits
the negation of the state, non-empty input always emits `false`. -/
theorem empty_run (q : Bool) (x : List Bool) :
    fstRun2 emptyD emptyFin q x = [decide (x = []) && !q] := by
  induction x generalizing q with
  | nil => cases q <;> rfl
  | cons a l ih => simp [fstRun2, emptyD, ih]

/-- From the start state the transducer emits `[decide (x = [])]`. -/
theorem empty_run_start (x : List Bool) :
    fstRun2 emptyD emptyFin false x = [decide (x = [])] := by
  cases x with
  | nil => rfl
  | cons a l => simp [fstRun2, emptyD, empty_run]

end PvsNP.Units.m2_tm_empty_test

/-- Testing whether a polynomial-time function's output is empty takes polynomial time
(TM2): the emptiness test is a two-state transducer (via the settled unit `fr_ladner`'s
`fst2_polyTime`), composed with `f` by the settled unit `m2_polytime_comp`. -/
theorem PvsNP.Units.m2_tm_empty_test :
    ∀ f : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f →
      PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
        (fun x : List Bool => decide (f x = [])) := by
  intro f hf
  have hEmpty : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun y : List Bool => decide (y = [])) :=
    fst2_polyTime _ _ _
      PvsNP.Units.m2_tm_empty_test.emptyD PvsNP.Units.m2_tm_empty_test.emptyFin false
      (fun y => by
        show [decide (y = [])] =
          fstRun2 PvsNP.Units.m2_tm_empty_test.emptyD
            PvsNP.Units.m2_tm_empty_test.emptyFin false y
        exact (PvsNP.Units.m2_tm_empty_test.empty_run_start y).symm)
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
    f (fun y : List Bool => decide (y = [])) hf hEmpty
