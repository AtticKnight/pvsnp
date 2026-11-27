import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_unary_pad_np
import PvsNP.Units.m2_exp_clock

/-
Adapted from `lean/PEqualNP/Library/Machines/FirstTime.lean`,
`lean/PEqualNP/Library/Helpers/PadMap.lean`,
`lean/PEqualNP/Library/Helpers/PadTest.lean`, and
`lean/PEqualNP/Library/Helpers/ExpBound.lean` in
https://github.com/open-goat/pequalnp-proofs
(commit `b41f8d5ee1b4d88356a61c2d848bf5bc13d0c387`, upstream of `8df87a862bd9a618faecf10ba65bff72706442c9`),
licensed under Apache-2.0.
Modified: assembled in namespace PvsNP.Units.m2_p_eq_np_nexp_exp using the settled campaign units
m2_unary_pad_np, m2_exp_clock, and fr_ladner to prove P = NP -> NEXP subset EXP.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_p_eq_np_nexp_exp

open Turing
open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Helpers

/-! ### Exponential growth bounds (`ExpBound`) -/

def ExpBound (f : ℕ → ℕ) : Prop :=
  ∃ A D : ℕ, ∀ n, f n ≤ 2 ^ (A * (n + 1) ^ D)

theorem eb_mono {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : ExpBound g) : ExpBound f := by
  obtain ⟨A, D, hA⟩ := hg
  exact ⟨A, D, fun n => (h n).trans (hA n)⟩

theorem eb_const (c : ℕ) : ExpBound (fun _ => c) :=
  ⟨c, 0, fun _ => by simpa using (Nat.lt_two_pow_self (n := c)).le⟩

private theorem exp_le_merge (A B D E n : ℕ) :
    A * (n + 1) ^ D + B * (n + 1) ^ E ≤ (A + B) * (n + 1) ^ (D + E) := by
  have h1 : (n + 1) ^ D ≤ (n + 1) ^ (D + E) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (n + 1) ^ E ≤ (n + 1) ^ (D + E) := Nat.pow_le_pow_right (by omega) (by omega)
  have := Nat.mul_le_mul_left A h1
  have := Nat.mul_le_mul_left B h2
  nlinarith

theorem eb_mul {f g : ℕ → ℕ} (hf : ExpBound f) (hg : ExpBound g) :
    ExpBound (fun n => f n * g n) := by
  obtain ⟨A, D, hA⟩ := hf
  obtain ⟨B, E, hB⟩ := hg
  refine ⟨A + B, D + E, fun n => ?_⟩
  calc f n * g n ≤ 2 ^ (A * (n + 1) ^ D) * 2 ^ (B * (n + 1) ^ E) :=
        Nat.mul_le_mul (hA n) (hB n)
    _ = 2 ^ (A * (n + 1) ^ D + B * (n + 1) ^ E) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ((A + B) * (n + 1) ^ (D + E)) :=
        Nat.pow_le_pow_right (by norm_num) (exp_le_merge A B D E n)

theorem eb_add {f g : ℕ → ℕ} (hf : ExpBound f) (hg : ExpBound g) :
    ExpBound (fun n => f n + g n) := by
  obtain ⟨A, D, hA⟩ := hf
  obtain ⟨B, E, hB⟩ := hg
  refine ⟨A + B + 1, D + E, fun n => ?_⟩
  have hm := exp_le_merge A B D E n
  have h1 : 1 ≤ (n + 1) ^ (D + E) := Nat.one_le_pow _ _ (by omega)
  have ha : (2 : ℕ) ^ (A * (n + 1) ^ D) ≤ 2 ^ ((A + B) * (n + 1) ^ (D + E)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb : (2 : ℕ) ^ (B * (n + 1) ^ E) ≤ 2 ^ ((A + B) * (n + 1) ^ (D + E)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc : (2 : ℕ) ^ ((A + B) * (n + 1) ^ (D + E)) * 2 ≤ 2 ^ ((A + B + 1) * (n + 1) ^ (D + E)) := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have := hA n
  have := hB n
  show f n + g n ≤ _
  omega

theorem eb_of_le_monomial {f : ℕ → ℕ} (A D : ℕ) (hf : ∀ n, f n ≤ A * (n + 1) ^ D) :
    ExpBound f :=
  ⟨A, D, fun n => (hf n).trans Nat.lt_two_pow_self.le⟩

theorem eb_id : ExpBound (fun n => n) :=
  eb_of_le_monomial 1 1 (fun n => by simp)

theorem eb_two_pow {f : ℕ → ℕ} (A D K : ℕ) (hf : ∀ n, f n ≤ A * (n + 1) ^ D) :
    ExpBound (fun n => 2 ^ (f n ^ K)) := by
  refine ⟨A ^ K, D * K, fun n => Nat.pow_le_pow_right (by norm_num) ?_⟩
  calc f n ^ K ≤ (A * (n + 1) ^ D) ^ K := Nat.pow_le_pow_left (hf n) K
    _ = A ^ K * (n + 1) ^ (D * K) := by rw [mul_pow, ← pow_mul]

theorem eb_poly (p : Polynomial ℕ) {f : ℕ → ℕ} (hf : ExpBound f) :
    ExpBound (fun n => p.eval (f n)) := by
  obtain ⟨s, hs⟩ := polynomial_le_pow_add p
  obtain ⟨A, D, hA⟩ := hf
  have h : ExpBound (fun n => (2 ^ (A * (n + 1) ^ D)) ^ s + s) := by
    refine eb_add ⟨A * s, D, fun n => ?_⟩ (eb_const s)
    show (2 ^ (A * (n + 1) ^ D)) ^ s ≤ _
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [mul_right_comm])
  exact eb_mono (fun n => (eval_mono p (hA n)).trans (hs _)) h

theorem eb_final {f : ℕ → ℕ} (hf : ExpBound f) : ∃ j, ∀ n, f n ≤ 2 ^ (n ^ j) + j := by
  obtain ⟨A, D, hA⟩ := hf
  refine ⟨A + 2 * D + f 0 + f 1, fun n => ?_⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · have : f n ≤ A + 2 * D + f 0 + f 1 := by
      have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl
      · generalize f 0 = a; generalize f 1 = b; omega
      · generalize f 0 = a; generalize f 1 = b; omega
    exact this.trans (Nat.le_add_left _ _)
  · have h1 : A ≤ n ^ A := by
      have h2 : A < 2 ^ A := Nat.lt_two_pow_self
      have h3 : 2 ^ A ≤ n ^ A := Nat.pow_le_pow_left h A
      omega
    have h4 : (n + 1) ^ D ≤ n ^ (2 * D) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left (by nlinarith) D
    have h5 : A * (n + 1) ^ D ≤ n ^ (A + 2 * D) := by
      rw [pow_add]; exact Nat.mul_le_mul h1 h4
    have h6 : n ^ (A + 2 * D) ≤ n ^ (A + 2 * D + f 0 + f 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h7 : (2 : ℕ) ^ (A * (n + 1) ^ D) ≤ 2 ^ (n ^ (A + 2 * D + f 0 + f 1)) :=
      Nat.pow_le_pow_right (by norm_num) (h5.trans h6)
    have := hA n
    omega

/-! ### Explicit linear-time transducers and clock pairing -/

theorem fst2_time {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin : Q → Option βΓ) (q₀ : Q) (h : ∀ a, eb (f a) = fstRun2 δ fin q₀ (ea a)) :
    ComputableInTime ea eb f (fun n => 2 * n + 3) := by
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

def sepδ : Bool → (Bool ⊕ Bool) → Bool × Option Bool × Option Bool
  | false, Sum.inl b => (false, some b, none)
  | false, Sum.inr b => (true, some false, some b)
  | true, Sum.inl b => (true, some b, none)
  | true, Sum.inr b => (true, some b, none)

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

theorem sepPair_time : ComputableInTime encodePair
    (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1 ++ false :: p.2)
    (fun n => 2 * n + 3) :=
  fst2_time _ _ _ sepδ sepFin false (fun p => (sep_run_false p.1 p.2).symm)

def consδ : Bool → Bool → Bool × Option Bool × Option Bool
  | false, b => (true, some true, some b)
  | true, b => (true, some b, none)

def consFin : Bool → Option Bool
  | false => some true
  | true => none

theorem cons_run_true (y : List Bool) : fstRun2 consδ consFin true y = y := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [fstRun2, consδ, ih]

theorem cons_run_false (y : List Bool) : fstRun2 consδ consFin false y = true :: y := by
  cases y with
  | nil => rfl
  | cons b y => simp [fstRun2, consδ, cons_run_true]

theorem consTrue_time : ComputableInTime (fun x : List Bool => x)
    (fun x : List Bool => x) (fun y : List Bool => true :: y) (fun n => 2 * n + 3) :=
  fst2_time _ _ _ consδ consFin false (fun y => (cons_run_false y).symm)

def consFδ : Bool → Bool → Bool × Option Bool × Option Bool
  | false, b => (true, some false, some b)
  | true, b => (true, some b, none)

def consFFin : Bool → Option Bool
  | false => some false
  | true => none

theorem consF_run_true (y : List Bool) : fstRun2 consFδ consFFin true y = y := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [fstRun2, consFδ, ih]

theorem consF_run_false (y : List Bool) : fstRun2 consFδ consFFin false y = false :: y := by
  cases y with
  | nil => rfl
  | cons b y => simp [fstRun2, consFδ, consF_run_true]

theorem consFalse_time : ComputableInTime (fun x : List Bool => x)
    (fun x : List Bool => x) (fun y : List Bool => false :: y) (fun n => 2 * n + 3) :=
  fst2_time _ _ _ consFδ consFFin false (fun y => (consF_run_false y).symm)

theorem clockPair_time : ∃ p : Polynomial ℕ, ∀ (t : ℕ → ℕ) (c : ℕ),
    ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (t x.length) true) (fun n => c * t n + c) →
    ComputableInTime (fun x : List Bool => x)
      encodePair
      (fun x : List Bool => (List.replicate (t x.length) true, x))
      (fun n => c * t n + c + 2 * t n + p.eval n) := by
  classical
  obtain ⟨pd, c1, hc1⟩ := time_of_polyTime cpt_dup
  refine ⟨pd + Polynomial.C 8 * Polynomial.X + Polynomial.C 7, ?_⟩
  rintro t c ⟨c2, hc2⟩
  let e₀ : Bool → c2.tm.Γ c2.tm.k₀ := c2.inputAlphabet.invFun
  let e₁ : c2.tm.Γ c2.tm.k₁ → Bool := c2.outputAlphabet
  let M2 : FinTM2 := firstM c2.tm e₀ e₁
  let φ : c1.tm.Γ c1.tm.k₁ → M2.Γ M2.k₀ := fun y => c1.outputAlphabet y
  let d : Option (M2.Γ M2.k₀) := some (Sum.inl true)
  have hd : d = none → IsEmpty (M2.Γ M2.k₀) := fun h => absurd h (Option.some_ne_none _)
  let T : ℕ → ℕ := fun n => c * t n + c + 2 * t n +
    (pd + Polynomial.C 8 * Polynomial.X + Polynomial.C 7).eval n
  have key : ∀ x : List Bool, ∃ n, n ≤ T x.length ∧
      (flip bind (TM2.step (prog c1.tm M2 φ d)))^[n]
          (some (initList (comp c1.tm M2 φ d) (List.map c1.inputAlphabet.invFun x))) =
        some (haltList (comp c1.tm M2 φ d)
          (encodePair (List.replicate (t x.length) true, x))) := by
    intro x
    have r1 := c1.outputsFun x
    have r2 := c2.outputsFun x
    obtain ⟨n2, hn2, hrun2⟩ := first_run e₀ e₁ x x _ r2.steps r2.evals_in_steps
    have hm : (List.map c2.outputAlphabet.invFun (List.replicate (t x.length) true)).map e₁ =
        List.replicate (t x.length) true := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (List.replicate (t x.length) true)]
      exact List.map_congr_left fun y _ => c2.outputAlphabet.right_inv y
    rw [hm] at hrun2
    have hφ : (List.map c1.outputAlphabet.invFun (encodePair (x, x))).map φ =
        encodePair (x, x) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (encodePair (x, x))]
      exact List.map_congr_left fun y _ => c1.outputAlphabet.right_inv y
    have h2 : (flip bind (TM2.step M2.m))^[n2]
        (some (initList M2 ((List.map c1.outputAlphabet.invFun (encodePair (x, x))).map φ))) =
        some (haltList M2 (encodePair (List.replicate (t x.length) true, x))) := by
      rw [hφ]; exact hrun2
    obtain ⟨n, hn, -, hrun⟩ := comp_run φ d hd _ _ _ r1.steps n2 r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 : r1.steps ≤ pd.eval x.length := r1.steps_le_m.trans (hc1 _)
    have b2 : r2.steps ≤ c * t x.length + c := r2.steps_le_m.trans (hc2 _)
    simp only [List.length_map, List.length_replicate, encodePair_length] at hn2 ⊢
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega
  exact ⟨{
    tm := comp c1.tm M2 φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun x =>
      { steps := Classical.choose (key x)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (Classical.choose_spec (key x)).2.trans
            (congrArg (fun l => some (haltList (comp c1.tm M2 φ d) l))
              (hm _ (encodePair (List.replicate (t x.length) true, x))).symm)
        steps_le_m := (Classical.choose_spec (key x)).1 } }, fun _ => le_rfl⟩

/-! ### Exponential padding map in `ExpBound` time -/

theorem pad_expBound (k : ℕ) :
    ∃ t : ℕ → ℕ, ExpBound t ∧
      ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) t := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h2 := comp_time (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => x)
      (fun y : List Bool => false :: y) (fun y : List Bool => true :: y)
      _ (fun n => 2 * n + 3) (fun n => n + 1) consFalse_time consTrue_time
      (fun _ _ h => by dsimp; omega) (fun x => by simp)
    have h3 := comp_time (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => x)
      (fun y : List Bool => true :: false :: y) (fun y : List Bool => true :: y)
      _ (fun n => 2 * n + 3) (fun n => n + 2) h2 consTrue_time
      (fun _ _ h => by dsimp; omega) (fun x => by simp)
    have hfn : (fun x : List Bool => List.replicate (2 ^ (x.length ^ 0) + 0) true ++ false :: x) =
        fun x : List Bool => true :: true :: false :: x := by
      funext x; simp [List.replicate]
    rw [hfn]
    refine ⟨_, ?_, h3⟩
    exact eb_of_le_monomial 25 1 (fun n => by simp only [pow_one]; omega)
  · obtain ⟨c0, M0, hM0⟩ := PvsNP.Units.m2_exp_clock k hk
    have hc0 : ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)
        (fun n => c0 * 2 ^ (n ^ k) + c0) := ⟨M0, hM0⟩
    obtain ⟨pd, hpd⟩ := clockPair_time
    have hA := hpd (fun n => 2 ^ (n ^ k)) c0 hc0
    have hB := comp_time (fun x : List Bool => x) encodePair (fun x : List Bool => x)
      (fun x : List Bool => (List.replicate (2 ^ (x.length ^ k)) true, x))
      (fun p : List Bool × List Bool => p.1 ++ false :: p.2)
      _ (fun n => 2 * n + 3) (fun n => 2 ^ (n ^ k) + n) hA sepPair_time
      (fun _ _ h => by dsimp; omega) (fun x => by
        change ((List.replicate (2 ^ x.length ^ k) true).map Sum.inl ++ x.map Sum.inr).length ≤ _
        simp)
    have hpow : ExpBound (fun n => 2 ^ (n ^ k)) := eb_two_pow 1 1 k (fun n => by simp)
    have hstep : ∀ j : ℕ, ∃ t : ℕ → ℕ, ExpBound t ∧
        ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + j) true ++ false :: x) t := by
      intro j
      induction j with
      | zero =>
        refine ⟨_, ?_, hB⟩
        have h1 : ExpBound (fun n => c0 * 2 ^ (n ^ k) + c0 + 2 * 2 ^ (n ^ k) + pd.eval n) :=
          eb_add (eb_add (eb_add (eb_mul (eb_const c0) hpow) (eb_const c0))
            (eb_mul (eb_const 2) hpow)) (eb_poly pd eb_id)
        have hlen : ExpBound (fun n => 2 ^ (n ^ k) + n) := eb_add hpow eb_id
        have h2 : ExpBound (fun n => 2 * (2 ^ (n ^ k) + n) + 2) :=
          eb_add (eb_mul (eb_const 2) hlen) (eb_const 2)
        have h3 : ExpBound (fun n => 2 * (2 ^ (n ^ k) + n) + 3) :=
          eb_add (eb_mul (eb_const 2) hlen) (eb_const 3)
        exact eb_add (eb_add h1 h2) h3
      | succ j ih =>
        obtain ⟨tj, htj, hcj⟩ := ih
        have hS := comp_time (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => x)
          (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + j) true ++ false :: x)
          (fun y : List Bool => true :: y)
          tj (fun n => 2 * n + 3) (fun n => 2 ^ (n ^ k) + j + 1 + n) hcj consTrue_time
          (fun _ _ h => by dsimp; omega) (fun x => by simp; omega)
        have hfn : (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + (j + 1)) true ++ false :: x) =
            fun x : List Bool => true :: (List.replicate (2 ^ (x.length ^ k) + j) true ++ false :: x) := by
          funext x
          rw [← Nat.add_assoc, List.replicate_succ, List.cons_append]
        rw [hfn]
        refine ⟨_, ?_, hS⟩
        have hlen : ExpBound (fun n => 2 ^ (n ^ k) + j + 1 + n) :=
          eb_add (eb_add (eb_add hpow (eb_const j)) (eb_const 1)) eb_id
        have h2 : ExpBound (fun n => 2 * (2 ^ (n ^ k) + j + 1 + n) + 2) :=
          eb_add (eb_mul (eb_const 2) hlen) (eb_const 2)
        have h3 : ExpBound (fun n => 2 * (2 ^ (n ^ k) + j + 1 + n) + 3) :=
          eb_add (eb_mul (eb_const 2) hlen) (eb_const 3)
        exact eb_add (eb_add htj h2) h3
    exact hstep k

theorem rep_false : ∀ (a b : ℕ) (u v : List Bool),
    List.replicate a true ++ false :: u = List.replicate b true ++ false :: v → a = b ∧ u = v
  | 0, 0, _, _, h => ⟨rfl, by simpa using h⟩
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | a + 1, b + 1, u, v, h => by
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at h
      have ⟨hab, huv⟩ := rep_false a b u v h.2
      exact ⟨congrArg Nat.succ hab, huv⟩

theorem p_eq_np_nexp_exp
    (hPN : PvsNP.P = PvsNP.NP) (L : Language Bool)
    (hNEXP : ∃ (V : List Bool × List Bool → Bool) (k : ℕ),
      PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
        ∀ x : List Bool, x ∈ L ↔
          ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) :
    ∃ k : ℕ, ∃ (f : List Bool → Bool)
        (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  obtain ⟨V, k, hV, hL⟩ := hNEXP
  let U : Language Bool :=
    {y : List Bool | ∃ (t : ℕ) (x w : List Bool),
      y = List.replicate t true ++ false :: x ∧ w.length ≤ t ∧ V (x, w) = true}
  have hUNP : U ∈ PvsNP.NP := PvsNP.Units.m2_unary_pad_np V hV
  have hUP : U ∈ PvsNP.P := hPN.symm ▸ hUNP
  obtain ⟨d, hd_cpt, hd_mem⟩ := hUP
  obtain ⟨p, hd_time⟩ := time_of_polyTime hd_cpt
  obtain ⟨tpad, htpad_eb, hpad_time⟩ := pad_expBound k
  let pad : List Bool → List Bool :=
    fun x => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x
  let len : ℕ → ℕ := fun n => 2 ^ (n ^ k) + k + 1 + n
  have hcomp := comp_time (fun x : List Bool => x) (fun x : List Bool => x) Computability.encodeBool
    pad d tpad (fun m => p.eval m) len hpad_time hd_time (fun _ _ h => eval_mono p h)
    (fun x => by simp [pad, len]; omega)
  have hpow : ExpBound (fun n => 2 ^ (n ^ k)) := eb_two_pow 1 1 k (fun n => by simp)
  have hlen_eb : ExpBound len :=
    eb_add (eb_add (eb_add hpow (eb_const k)) (eb_const 1)) eb_id
  have htot_eb : ExpBound (fun n => tpad n + (2 * len n + 2) + p.eval (len n)) :=
    eb_add (eb_add htpad_eb (eb_add (eb_mul (eb_const 2) hlen_eb) (eb_const 2))) (eb_poly p hlen_eb)
  obtain ⟨J, hJ⟩ := eb_final htot_eb
  obtain ⟨M, hM⟩ := hcomp
  refine ⟨J, fun x => d (pad x), M, fun x => ?_, fun n => (hM n).trans (hJ n)⟩
  rw [hL x, ← hd_mem (pad x)]
  constructor
  · rintro ⟨w, hw, hVxw⟩
    exact ⟨2 ^ (x.length ^ k) + k, x, w, rfl, hw, hVxw⟩
  · rintro ⟨t, x', w, heq, hw, hVxw⟩
    obtain ⟨ht, hx⟩ := rep_false _ _ _ _ heq
    subst hx
    rw [← ht] at hw
    exact ⟨w, hw, hVxw⟩

end PvsNP.Units.m2_p_eq_np_nexp_exp

theorem PvsNP.Units.m2_p_eq_np_nexp_exp :
    PvsNP.P = PvsNP.NP → ∀ L : Language Bool,
      (∃ (V : List Bool × List Bool → Bool) (k : ℕ),
        PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer V ∧
          ∀ x : List Bool, x ∈ L ↔ ∃ w : List Bool, w.length ≤ 2 ^ (x.length ^ k) + k ∧ V (x, w) = true) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.m2_p_eq_np_nexp_exp.p_eq_np_nexp_exp
