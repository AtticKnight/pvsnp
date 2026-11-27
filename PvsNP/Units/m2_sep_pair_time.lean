import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

namespace PvsNP.Units.m2_sep_pair_time

open Turing PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

/-- Transducer writing the separator at the first symbol of the second component. -/
def sepδ : Bool → (Bool ⊕ Bool) → Bool × Option Bool × Option Bool
  | false, Sum.inl b => (false, some b, none)
  | false, Sum.inr b => (true, some false, some b)
  | true, Sum.inl b => (true, some b, none)
  | true, Sum.inr b => (true, some b, none)

/-- End of input: write the separator if it was not written. -/
def sepFin : Bool → Option Bool
  | false => some false
  | true => none

theorem sep_run_true (x : List Bool) : fstRun2 sepδ sepFin true (x.map Sum.inr) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [fstRun2, sepδ, ih]

theorem sep_run_false (a x : List Bool) :
    fstRun2 sepδ sepFin false (a.map Sum.inl ++ x.map Sum.inr) = a ++ false :: x := by
  induction a with
  | nil =>
    cases x with
    | nil => rfl
    | cons b x => simp [fstRun2, sepδ, sep_run_true]
  | cons b a ih => simp [fstRun2, sepδ, ih]

/-- A transducer function is computable within `2 * n + 3` steps: `fst2_polyTime`
with the time bound kept explicit. -/
theorem fst2_time {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin : Q → Option βΓ) (q₀ : Q) (h : ∀ a, eb (f a) = fstRun2 δ fin q₀ (ea a)) :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime ea eb f (fun n => 2 * n + 3) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ _ : βΓ, d ≠ none := by
    intro y
    have hn : Nonempty βΓ := ⟨y⟩
    simp [d, hn]
  exact ⟨{
    tm := trM δ fin q₀ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => 2 * n + 3
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := trM_run δ fin q₀ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
            1 + 1 + ((ea a).length + 1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by omega } }, fun _ => le_rfl⟩

/-- The pair `(a, x)`, in the pair encoding, goes to `a ++ false :: x` within `2 * n + 3` steps. -/
theorem sepPair_time : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime PvsNP.encodePair
    PvsNP.encodeString (fun p : List Bool × List Bool => p.1 ++ false :: p.2)
    (fun n => 2 * n + 3) :=
  fst2_time _ _ _ sepδ sepFin false (fun p => (sep_run_false p.1 p.2).symm)

end PvsNP.Units.m2_sep_pair_time

theorem PvsNP.Units.m2_sep_pair_time :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString
        (fun p : List Bool × List Bool => p.1 ++ false :: p.2),
      ∀ n : ℕ, M.time n ≤ 2 * n + 3 :=
  PvsNP.Units.m2_sep_pair_time.sepPair_time
