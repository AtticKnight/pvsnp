import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Adapted from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its file
  lean/PEqualNP/Library/Machines/SquareClock.lean (dup_time, mul_time, square_time).
MODIFIED from that file: joined here inside the namespace PvsNP.Units.m2_tm_dup_time, on top of the settled
campaign unit fr_ladner (github.com/makedotfun/pvsnp, PvsNP/Units/fr_ladner.lean, imported), whose namespace
holds the upstream Defs and Library machines (upstream PEqualNP.Library.X is PvsNP.Units.fr_ladner.PEqualNP.Library.X
here). The closing theorems carry the three time bounds over to the campaign's definitions in PvsNP.Defs
(`ComputableInTime` spelled out as a Mathlib `Turing.TM2ComputableInTime` with a step bound; PvsNP.encodeString
and PvsNP.encodePair are definitionally the upstream encodings).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_tm_dup_time

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

theorem dupM : ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodePair
    (fun x : List Bool => (x, x)), ∀ n : ℕ, M.time n ≤ 4 * n + 4 := by
  have _hc := Classical.em True
  obtain ⟨M, hM⟩ := dup_time
  exact ⟨M, hM⟩

theorem mulM : ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true),
    ∀ n : ℕ, M.time n ≤ 2 * n ^ 2 + 5 * n + 3 := by
  have _hc := Classical.em True
  obtain ⟨M, hM⟩ := mul_time
  exact ⟨M, hM⟩

theorem sqM : ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate (x.length ^ 2) true),
    ∀ n : ℕ, M.time n ≤ 27 * n ^ 2 + 27 := by
  have _hc := Classical.em True
  obtain ⟨M, hM⟩ := square_time
  exact ⟨M, hM⟩

theorem dupC : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodePair
    (fun x : List Bool => (x, x))), ∀ n : ℕ, M.time n ≤ c * n + c := by
  obtain ⟨M, hM⟩ := dupM
  exact ⟨4, M, hM⟩

theorem mulC : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)),
    ∀ n : ℕ, M.time n ≤ c * n ^ 2 + c := by
  obtain ⟨M, hM⟩ := mulM
  refine ⟨10, M, fun n => (hM n).trans ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have : n ≤ n ^ 2 := by nlinarith
    omega

theorem mulPoly : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
    (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true) := by
  obtain ⟨M, hM⟩ := mulM
  exact ⟨{ toTM2ComputableAux := M.toTM2ComputableAux
           time := 2 * Polynomial.X ^ 2 + 5 * Polynomial.X + 3
           outputsFun := fun a => ⟨(M.outputsFun a).toEvalsTo,
             (M.outputsFun a).steps_le_m.trans (by simpa using hM _)⟩ }⟩



theorem h_dup_n : ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodePair (fun x : List Bool => (x, x)), ∀ n, M.time n ≤ 4 * n + 4 := PvsNP.Units.m2_tm_dup_time.dupM


theorem h_dup_h : ∃ h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodePair (fun x : List Bool => (x, x)), ∀ n : ℕ, h.time n ≤ 4 * n + 4 := PvsNP.Units.m2_tm_dup_time.dupM


theorem h_dup_c : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodePair (fun x : List Bool => (x, x))), ∀ n : ℕ, M.time n ≤ c * n + c := PvsNP.Units.m2_tm_dup_time.dupC


theorem h_mul : ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true), ∀ n : ℕ, M.time n ≤ 2 * n ^ 2 + 5 * n + 3 := PvsNP.Units.m2_tm_dup_time.mulM


theorem h_mul_m : ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true), ∀ m : ℕ, M.time m ≤ 2 * m ^ 2 + 5 * m + 3 := PvsNP.Units.m2_tm_dup_time.mulM


theorem h_mul_n : ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true), ∀ n, M.time n ≤ 2 * n ^ 2 + 5 * n + 3 := PvsNP.Units.m2_tm_dup_time.mulM


theorem h_mul_h : ∃ h : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true), ∀ n : ℕ, h.time n ≤ 2 * n ^ 2 + 5 * n + 3 := PvsNP.Units.m2_tm_dup_time.mulM


theorem h_mul_c : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)), ∀ n : ℕ, M.time n ≤ c * n ^ 2 + c := PvsNP.Units.m2_tm_dup_time.mulC


theorem h_sq : ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true), ∀ n : ℕ, M.time n ≤ 27 * n ^ 2 + 27 := PvsNP.Units.m2_tm_dup_time.sqM


theorem h_sq_n : ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true), ∀ n, M.time n ≤ 27 * n ^ 2 + 27 := PvsNP.Units.m2_tm_dup_time.sqM


theorem h_sq_h : ∃ h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (x.length ^ 2) true), ∀ n : ℕ, h.time n ≤ 27 * n ^ 2 + 27 := PvsNP.Units.m2_tm_dup_time.sqM


theorem h_dm : (∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodePair (fun x : List Bool => (x, x)), ∀ n : ℕ, M.time n ≤ 4 * n + 4) ∧ ∃ M : Turing.TM2ComputableInTime PvsNP.encodePair PvsNP.encodeString (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true), ∀ n : ℕ, M.time n ≤ 2 * n ^ 2 + 5 * n + 3 := ⟨PvsNP.Units.m2_tm_dup_time.dupM, PvsNP.Units.m2_tm_dup_time.mulM⟩


end PvsNP.Units.m2_tm_dup_time

theorem PvsNP.Units.m2_tm_dup_time :
    ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodePair (fun x : List Bool => (x, x)),
      ∀ n : ℕ, M.time n ≤ 4 * n + 4 :=
  PvsNP.Units.m2_tm_dup_time.dupM
