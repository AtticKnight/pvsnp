import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Adapted from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its files
  lean/PEqualNP/Library/Helpers/PadMap.lean (fst2_time) and
  lean/PEqualNP/Library/L100.lean (the statement and its proof).
MODIFIED from those files: joined here inside the namespace PvsNP.Units.m2_linear_clock, on top of the settled campaign
unit fr_ladner (github.com/makedotfun/pvsnp, PvsNP/Units/fr_ladner.lean, imported), whose namespace holds the
upstream Defs and Library machines (upstream PEqualNP.Library.X is PvsNP.Units.fr_ladner.PEqualNP.Library.X here).
The closing theorems carry upstream L100 over to the campaign's definitions in PvsNP.Defs (`ComputableInTime` spelled
out as a Mathlib `Turing.TM2ComputableInTime` with a step bound; PvsNP.encodeString is definitionally the upstream
encoding `fun x => x`); the polynomial-time corollaries are new.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_linear_clock

open Turing PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

/-- A transducer function is computable within `2 * n + 3` steps (upstream Helpers/PadMap). -/
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

/-- Upstream L100: a one-state transducer writes one `true` per input symbol. -/
theorem L100 : ∃ c : ℕ, PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime
    (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => List.replicate x.length true) (fun n : ℕ => c * n + c) := by
  refine ⟨3, ?_⟩
  obtain ⟨c, hc⟩ := fst2_time (fun x : List Bool => x)
    (fun x : List Bool => x) (fun x : List Bool => List.replicate x.length true)
    (fun (_ : Unit) (_ : Bool) => ((), some true, none)) (fun _ => none) ()
    (fun a => by
      induction a with
      | nil => rfl
      | cons b l ih =>
        simp only [List.length_cons, List.replicate_succ, fstRun2]
        simpa using ih)
  exact ⟨c, fun n => (hc n).trans (by show 2 * n + 3 ≤ 3 * n + 3; omega)⟩

/-- A machine with a step bound below a polynomial is a polynomial-time machine. -/
def polyOfTime {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (M : Turing.TM2ComputableInTime ea eb f) (p : Polynomial ℕ) (h : ∀ n, M.time n ≤ p.eval n) :
    Turing.TM2ComputableInPolyTime ea eb f where
  toTM2ComputableAux := M.toTM2ComputableAux
  time := p
  outputsFun := fun a => ⟨(M.outputsFun a).toEvalsTo, (M.outputsFun a).steps_le_m.trans (h _)⟩

theorem main : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate x.length true)), ∀ n : ℕ, M.time n ≤ c * n + c := by
  obtain ⟨c, M, hM⟩ := L100
  exact ⟨c, M, hM⟩

theorem main_swap : ∃ (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate x.length true)) (c : ℕ), ∀ n : ℕ, M.time n ≤ c * n + c := by
  obtain ⟨c, M, hM⟩ := main
  exact ⟨M, c, hM⟩

theorem main_polyc : ∃ (c : ℕ) (M : Turing.TM2ComputableInPolyTime PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => List.replicate x.length true)),
    ∀ n : ℕ, M.time.eval n ≤ c * n + c := by
  obtain ⟨c, M, hM⟩ := main
  refine ⟨c, polyOfTime M (Polynomial.C c * Polynomial.X + Polynomial.C c) (fun n => ?_), fun n => ?_⟩
  · simpa using hM n
  · simp [polyOfTime]

theorem main_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate x.length true) := by
  obtain ⟨c, M, -⟩ := main_polyc
  exact ⟨M⟩



theorem h_ex2 :
    ∃ c : ℕ, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true), ∀ n : ℕ, M.time n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main


theorem h_ex2n :
    ∃ c : ℕ, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true), ∀ n, M.time n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main


theorem h_n :
    ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true)), ∀ n, M.time n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main


theorem h_h :
    ∃ (c : ℕ) (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true)), ∀ n, h.time n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main


theorem h_hN :
    ∃ (c : ℕ) (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true)), ∀ n : ℕ, h.time n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main


theorem h_ex2h :
    ∃ c : ℕ, ∃ h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true), ∀ n, h.time n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main


theorem h_ex2hN :
    ∃ c : ℕ, ∃ h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true), ∀ n : ℕ, h.time n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main


theorem h_hc :
    ∃ (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true)) (c : ℕ), ∀ n, h.time n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main_swap


theorem h_hcN :
    ∃ (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true)) (c : ℕ), ∀ n : ℕ, h.time n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main_swap


theorem h_Mc :
    ∃ (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true)) (c : ℕ), ∀ n : ℕ, M.time n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main_swap


theorem h_polyc :
    ∃ (c : ℕ) (M : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true)), ∀ n : ℕ, M.time.eval n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main_polyc


theorem h_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate x.length true) :=
  PvsNP.Units.m2_linear_clock.main_poly


end PvsNP.Units.m2_linear_clock

theorem PvsNP.Units.m2_linear_clock :
    ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => List.replicate x.length true)), ∀ n : ℕ, M.time n ≤ c * n + c :=
  PvsNP.Units.m2_linear_clock.main
