import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Adapted from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its files
  lean/PEqualNP/Library/Machines/SquareClock.lean (dup_time, mul_time, square_time) and
  lean/PEqualNP/Library/L101.lean (the statement and its proof).
MODIFIED from those files: joined here inside the namespace PvsNP.Units.m2_square_clock, on top of the settled campaign
unit fr_ladner (github.com/makedotfun/pvsnp, PvsNP/Units/fr_ladner.lean, imported), whose namespace holds the
upstream Defs and Library machines (upstream PEqualNP.Library.X is PvsNP.Units.fr_ladner.PEqualNP.Library.X here,
written with that full name). The closing theorems carry upstream L101 over to the campaign's definitions in
PvsNP.Defs (`ComputableInTime` spelled out as a Mathlib `Turing.TM2ComputableInTime` with a step bound;
PvsNP.encodeString is definitionally the upstream encoding `fun x => x`); the polynomial-time corollaries are new.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_square_clock

open Turing PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

/-- Duplicating a string takes `4 * n + 4` steps. -/
theorem dup_time :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun x : List Bool => (x, x)) (fun n : ℕ => 4 * n + 4) := by
  let φ₁ : Bool → Option (Bool ⊕ Bool) := fun b => some (Sum.inl b)
  let φ₂ : Bool → Option (Bool ⊕ Bool) := fun b => some (Sum.inr b)
  let d : Option (Bool ⊕ Bool) := some (Sum.inl true)
  have hd : ∀ φ : Bool → Option (Bool ⊕ Bool), d = none → ∀ x, φ x = none :=
    fun φ h => by simp [d] at h
  have hid : ∀ x : List Bool, PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (x, x) =
      x.filterMap φ₁ ++ x.filterMap φ₂ := by
    intro x
    have h1 : x.filterMap φ₁ = x.map Sum.inl := by
      simp [φ₁]
    have h2 : x.filterMap φ₂ = x.map Sum.inr := by
      simp [φ₂]
    rw [h1, h2]; rfl
  exact ⟨{
    tm := tp φ₁ φ₂ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => 4 * n + 4
    outputsFun := fun a =>
      { steps := a.length + 1 + (a.length + 1) + (a.length + 1) + (a.length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) a
          exact (congrArg (fun l => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[a.length + 1 +
            (a.length + 1) + (a.length + 1) + (a.length + 1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm Bool a)).trans
            (this.trans (congrArg (fun l => some (haltList (tp φ₁ φ₂ d) l))
              ((hid a).symm.trans
                (hm _ (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (a, a))).symm)))
        steps_le_m := by
          show _ ≤ 4 * a.length + 4
          omega } }, fun _ => le_rfl⟩

/-- Unary multiplication of the lengths of a pair takes at most `2 * m ^ 2 + 5 * m + 3` steps
on a pair of total length `m`. -/
theorem mul_time :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)
      (fun m : ℕ => 2 * m ^ 2 + 5 * m + 3) := by
  exact ⟨{
    tm := mulTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun m => 2 * m ^ 2 + 5 * m + 3
    outputsFun := fun p =>
      { steps := mulSteps p.1.length p.2.length
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := mul_run p.1 p.2
          exact (congrArg (fun l => (flip bind (TM2.step mulProg))^[mulSteps p.1.length
            p.2.length] (some (initList mulTM l)))
              (hm _ (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair p))).trans
            (this.trans (congrArg (fun l => some (haltList mulTM l)) (hm Bool _).symm))
        steps_le_m := by
          simp only [PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair, List.length_append,
            List.length_map, mulSteps]
          nlinarith [Nat.zero_le (p.1.length * p.1.length),
            Nat.zero_le (p.2.length * p.2.length), Nat.zero_le (p.1.length * p.2.length)] } },
    fun _ => le_rfl⟩

/-- The quadratic clock with an explicit constant. -/
theorem square_time :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.length ^ 2) true)
      (fun n : ℕ => 27 * n ^ 2 + 27) := by
  have h := comp_time (fun x : List Bool => x) PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
    (fun x : List Bool => x) (fun x : List Bool => (x, x))
    (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)
    (fun n : ℕ => 4 * n + 4) (fun m : ℕ => 2 * m ^ 2 + 5 * m + 3) (fun n : ℕ => 2 * n)
    dup_time mul_time
    (fun a b hab => by
      have := Nat.pow_le_pow_left hab 2
      show 2 * a ^ 2 + 5 * a + 3 ≤ 2 * b ^ 2 + 5 * b + 3
      omega)
    (fun a => by simp [PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair]; omega)
  have h' : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.length ^ 2) true)
      (fun n : ℕ => 4 * n + 4 + (2 * (2 * n) + 2) + (2 * (2 * n) ^ 2 + 5 * (2 * n) + 3)) := by
    simpa only [sq] using h
  refine time_mono h' fun n => ?_
  nlinarith [Nat.zero_le (n * n), Nat.le_mul_self n]

/-- Upstream L101: the quadratic clock. -/
theorem L101 : ∃ c : ℕ, PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime
    (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => List.replicate (x.length ^ 2) true) (fun n : ℕ => c * n ^ 2 + c) :=
  ⟨27, square_time⟩

/-- A machine with a step bound below a polynomial is a polynomial-time machine. -/
def polyOfTime {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (M : Turing.TM2ComputableInTime ea eb f) (p : Polynomial ℕ) (h : ∀ n, M.time n ≤ p.eval n) :
    Turing.TM2ComputableInPolyTime ea eb f where
  toTM2ComputableAux := M.toTM2ComputableAux
  time := p
  outputsFun := fun a => ⟨(M.outputsFun a).toEvalsTo, (M.outputsFun a).steps_le_m.trans (h _)⟩

theorem main : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate (x.length ^ 2) true)), ∀ n : ℕ, M.time n ≤ c * n ^ 2 + c := by
  obtain ⟨c, M, hM⟩ := L101
  exact ⟨c, M, hM⟩

theorem main_swap : ∃ (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate (x.length ^ 2) true)) (c : ℕ),
    ∀ n : ℕ, M.time n ≤ c * n ^ 2 + c := by
  obtain ⟨c, M, hM⟩ := main
  exact ⟨M, c, hM⟩

theorem main_polyc : ∃ (c : ℕ) (M : Turing.TM2ComputableInPolyTime PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true)),
    ∀ n : ℕ, M.time.eval n ≤ c * n ^ 2 + c := by
  obtain ⟨c, M, hM⟩ := main
  refine ⟨c, polyOfTime M (Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C c) (fun n => ?_),
    fun n => ?_⟩
  · simpa using hM n
  · simp [polyOfTime]

theorem main_poly : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate (x.length ^ 2) true) := by
  obtain ⟨c, M, -⟩ := main_polyc
  exact ⟨M⟩



theorem h_ex2 :
    ∃ c : ℕ, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true), ∀ n : ℕ, M.time n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main


theorem h_ex2n :
    ∃ c : ℕ, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true), ∀ n, M.time n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main


theorem h_n :
    ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true)), ∀ n, M.time n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main


theorem h_h :
    ∃ (c : ℕ) (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true)), ∀ n, h.time n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main


theorem h_hN :
    ∃ (c : ℕ) (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true)), ∀ n : ℕ, h.time n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main


theorem h_ex2h :
    ∃ c : ℕ, ∃ h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true), ∀ n, h.time n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main


theorem h_ex2hN :
    ∃ c : ℕ, ∃ h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true), ∀ n : ℕ, h.time n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main


theorem h_hc :
    ∃ (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true)) (c : ℕ), ∀ n, h.time n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main_swap


theorem h_hcN :
    ∃ (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true)) (c : ℕ), ∀ n : ℕ, h.time n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main_swap


theorem h_Mc :
    ∃ (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true)) (c : ℕ), ∀ n : ℕ, M.time n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main_swap


theorem h_polyc :
    ∃ (c : ℕ) (M : Turing.TM2ComputableInPolyTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true)), ∀ n : ℕ, M.time.eval n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main_polyc


theorem h_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true) :=
  PvsNP.Units.m2_square_clock.main_poly


end PvsNP.Units.m2_square_clock

theorem PvsNP.Units.m2_square_clock :
    ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => List.replicate (x.length ^ 2) true)), ∀ n : ℕ, M.time n ≤ c * n ^ 2 + c :=
  PvsNP.Units.m2_square_clock.main
