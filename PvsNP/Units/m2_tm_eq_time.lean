import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_eq_polytime

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_eq_time

open Turing PvsNP.Units.m2_eq_polytime

/-- The pair writing of `m2_eq_polytime` (private there), written again here. -/
def gp (p : List Bool × List Bool) : List (Bool ⊕ Bool) :=
  p.1.map Sum.inl ++ p.2.map Sum.inr

theorem eq_run' (p : List Bool × List Bool) :
    ∃ n, n ≤ 2 * (gp (p.1, p.2)).length + 2 ∧
      eqStep^[n] (some (initList (eqM Bool) (gp (p.1, p.2)))) =
        some (haltList (eqM Bool) [decide (p.1 = p.2)]) :=
  eq_run p

/-- The settled machine `eqM Bool`, kept as data so its time polynomial stays visible. -/
noncomputable def eqPoly :
    Turing.TM2ComputableInPolyTime
      (fun p : List Bool × List Bool => gp (p.1, p.2))
      Computability.encodeBool (fun p : List Bool × List Bool => decide (p.1 = p.2)) :=
  { tm := eqM Bool
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
    outputsFun := fun p =>
      { steps := Classical.choose (eq_run' p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [decide (p.1 = p.2)] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool (decide (p.1 = p.2))) := by
            rw [hm]
            rfl
          exact (congrArg (fun x => eqStep^[Classical.choose (eq_run' p)]
            (some (initList (eqM Bool) x))) (hm _ (gp (p.1, p.2)))).trans
            ((Classical.choose_spec (eq_run' p)).2.trans
              (congrArg (fun x => some (haltList (eqM Bool) x)) hout))
        steps_le_m := by
          have h := (Classical.choose_spec (eq_run' p)).1
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          exact h } }

theorem gp_eq_encodePair :
    (fun p : List Bool × List Bool => gp (p.1, p.2)) = PvsNP.encodePair := by
  funext ⟨x, y⟩
  simp [gp, PvsNP.encodePair, Computability.encodingProd, Computability.encodingList]

theorem eq_time_gp :
    ∃ M : Turing.TM2ComputableInTime
        (fun p : List Bool × List Bool => gp (p.1, p.2)) PvsNP.encodeAnswer
        (fun p : List Bool × List Bool => decide (p.1 = p.2)),
      ∀ n : ℕ, M.time n ≤ 2 * n + 2 := by
  refine ⟨eqPoly.toTM2ComputableInTime, fun n => ?_⟩
  simp [Turing.TM2ComputableInPolyTime.toTM2ComputableInTime, eqPoly]

theorem eq_time :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeAnswer
        (fun p : List Bool × List Bool => decide (p.1 = p.2)),
      ∀ n : ℕ, M.time n ≤ 2 * n + 2 := by
  have h := eq_time_gp
  rw [gp_eq_encodePair] at h
  exact h

end PvsNP.Units.m2_tm_eq_time

theorem PvsNP.Units.m2_tm_eq_time :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeAnswer
        (fun p : List Bool × List Bool => decide (p.1 = p.2)), ∀ n : ℕ, M.time n ≤ 2 * n + 2 :=
  PvsNP.Units.m2_tm_eq_time.eq_time
