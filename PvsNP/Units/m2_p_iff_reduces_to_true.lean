import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Built on the settled unit PvsNP.Units.fr_ladner of github.com/makedotfun/pvsnp (Apache License
2.0), which this file imports: its machines are those of github.com/brilliant-hq/pequalnp-proofs
at commit 8df87a862bd9a618faecf10ba65bff72706442c9 (Apache License 2.0).
-/

namespace PvsNP.Units.m2_p_iff_reduces_to_true

/-- The transducer that answers whether its input is `[true]`: state 0 at the start, 1 after a
first `true`, 2 once the input can no longer be `[true]`. -/
def isTrueD : Fin 3 → Bool → Fin 3 × Option Bool
  | 0, true => (1, none)
  | _, _ => (2, none)

def isTrueFin : Fin 3 → Option Bool
  | 1 => some true
  | _ => some false

theorem run_dead (l : List Bool) : PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun isTrueD isTrueFin 2 l = [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simpa [PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun, isTrueD] using ih

theorem run_isTrue (x : List Bool) :
    Computability.encodeBool (decide (x = [true])) = PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun isTrueD isTrueFin 0 x := by
  rcases x with _ | ⟨b, l⟩
  · rfl
  · cases b
    · simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun, isTrueD, run_dead, Computability.encodeBool]
    · rcases l with _ | ⟨c, l⟩
      · rfl
      · cases c <;> simp [PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fstRun, isTrueD, run_dead, Computability.encodeBool]

/-- Deciding whether the input is `[true]` takes polynomial time. -/
theorem cpt_isTrue :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => decide (x = [true])) :=
  PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.fst_polyTime (fun x : List Bool => x) Computability.encodeBool _ isTrueD isTrueFin 0
    run_isTrue

end PvsNP.Units.m2_p_iff_reduces_to_true

/-- A language is in P exactly when it reduces to the language `{[true]}` (TM2): a decider's
answer, written as a string, is the reduction; conversely, decide the reduction's output. -/
theorem PvsNP.Units.m2_p_iff_reduces_to_true :
    ∀ L : Language Bool, L ∈ PvsNP.P ↔
      PvsNP.KarpReducible L ({x : List Bool | x = [true]} : Language Bool) := by
  intro L
  constructor
  · rintro ⟨d, ⟨c⟩, hdec⟩
    refine ⟨fun x => [d x], ⟨⟨c.toTM2ComputableAux, c.time, c.outputsFun⟩⟩, fun x => ?_⟩
    show x ∈ L ↔ [d x] = [true]
    rw [hdec x]
    simp
  · rintro ⟨f, hf, hred⟩
    refine ⟨fun x => decide (f x = [true]), PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp hf PvsNP.Units.m2_p_iff_reduces_to_true.cpt_isTrue,
      fun x => ?_⟩
    rw [hred x]
    show f x = [true] ↔ _
    simp
