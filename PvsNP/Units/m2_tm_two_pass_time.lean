import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_two_pass_polytime

/-
Two filter-map passes over a string take at most `4 * n + 4` steps.

The machine is the one of the settled unit `PvsNP.Units.m2_two_pass_polytime` (imported, not
copied in spirit: the construction below is the `twoPass_polyTime` construction specialised to
`Bool` and `PvsNP.encodeString`, so that the resulting `TM2ComputableInPolyTime` is a concrete
structure whose `time` field is definitionally `Polynomial.C 4 * Polynomial.X +
Polynomial.C 4`). Read as a timed machine by Mathlib's
`Turing.TM2ComputableInPolyTime.toTM2ComputableInTime`, its time at `n` is `(C 4 * X + C 4).eval n
= 4 * n + 4`.
-/

namespace PvsNP.Units.m2_tm_two_pass_time

open Turing

/-- The two-pass machine of `PvsNP.Units.m2_two_pass_polytime`, with its polynomial time bound,
as a concrete `TM2ComputableInPolyTime` (so its `time` field reduces to `C 4 * X + C 4`). -/
noncomputable def twoPassPoly (φ₁ φ₂ : Bool → Option Bool) :
    Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => x.filterMap φ₁ ++ x.filterMap φ₂) := by
  classical
  let d : Option Bool := if h : Nonempty Bool then some (Classical.choice h) else none
  have hd : ∀ φ : Bool → Option Bool, d = none → ∀ x, φ x = none := by
    intro φ hdn x
    by_cases hn : Nonempty Bool
    · simp [d, hn] at hdn
    · cases hφ : φ x with
      | none => rfl
      | some y => exact absurd ⟨y⟩ hn
  have h : ∀ a : List Bool,
      PvsNP.encodeString ((fun x : List Bool => x.filterMap φ₁ ++ x.filterMap φ₂) a) =
        (PvsNP.encodeString a).filterMap φ₁ ++ (PvsNP.encodeString a).filterMap φ₂ :=
    fun _ => rfl
  exact {
    tm := PvsNP.Units.m2_two_pass_polytime.tp φ₁ φ₂ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 4
    outputsFun := fun a =>
      { steps := (PvsNP.encodeString a).length + 1 + ((PvsNP.encodeString a).length + 1) +
          ((PvsNP.encodeString a).length + 1) + ((PvsNP.encodeString a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hrun := PvsNP.Units.m2_two_pass_polytime.tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂)
            (PvsNP.encodeString a)
          exact (congrArg (fun l => (flip bind (TM2.step (PvsNP.Units.m2_two_pass_polytime.tpProg φ₁ φ₂ d)))^[(PvsNP.encodeString a).length + 1 +
            ((PvsNP.encodeString a).length + 1) + ((PvsNP.encodeString a).length + 1) + ((PvsNP.encodeString a).length + 1)]
            (some (initList (PvsNP.Units.m2_two_pass_polytime.tp φ₁ φ₂ d) l))) (hm Bool (PvsNP.encodeString a))).trans
            (hrun.trans (congrArg (fun l => some (haltList (PvsNP.Units.m2_two_pass_polytime.tp φ₁ φ₂ d) l))
              ((h a).symm.trans (hm Bool (PvsNP.encodeString ((fun x : List Bool => x.filterMap φ₁ ++ x.filterMap φ₂) a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }

end PvsNP.Units.m2_tm_two_pass_time

/-- Two filter-map passes over a string take at most `4 * n + 4` steps. -/
theorem PvsNP.Units.m2_tm_two_pass_time :
    ∀ φ₁ φ₂ : Bool → Option Bool,
      ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
          (fun x : List Bool => x.filterMap φ₁ ++ x.filterMap φ₂),
        ∀ n : ℕ, M.time n ≤ 4 * n + 4 := by
  intro φ₁ φ₂
  refine ⟨PvsNP.Units.m2_tm_two_pass_time.twoPassPoly φ₁ φ₂ |>.toTM2ComputableInTime,
    fun n => ?_⟩
  change (Polynomial.C 4 * Polynomial.X + Polynomial.C 4 : Polynomial ℕ).eval n ≤ 4 * n + 4
  simp
