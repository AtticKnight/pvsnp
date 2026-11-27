import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner

/-
Adapted from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its files
  lean/PEqualNP/Library/Helpers/ExpDoubling.lean (the doubling machine, dbl_time),
  lean/PEqualNP/Library/Helpers/PolyBelowExp.lean (polynomial_le_two_pow_pow_add_const),
  lean/PEqualNP/Library/Helpers/PadMap.lean (fst2_time, sepPair_time, consTrue_time),
  lean/PEqualNP/Library/Machines/FirstTime.lean (clockPair_time),
  lean/PEqualNP/Library/L083.lean and
  lean/PEqualNP/Library/L094.lean (the statements and their proofs).
MODIFIED from those files: joined here in that order inside the namespace PvsNP.Units.m2_padded_exp_clock, on top of the
settled campaign unit fr_ladner (github.com/makedotfun/pvsnp, PvsNP/Units/fr_ladner.lean, imported), in whose
namespace the upstream Defs and Library machines live (upstream PEqualNP.Library.X is
PvsNP.Units.fr_ladner.PEqualNP.Library.X here, written with that full name); a reducible def is an abbrev.
The closing theorems carry upstream L083 and L094 over to the campaign's definitions in PvsNP.Defs
(`ComputableInTime` spelled out as a Mathlib `Turing.TM2ComputableInTime` with a step bound; PvsNP.encodeString is
definitionally the upstream encoding `fun x => x`); the corollaries are new.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_padded_exp_clock

open Turing PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

/-! ## Upstream Helpers/ExpDoubling: a machine that writes `2 ^ |x|` ones -/

inductive DblK
  | I | B | O
  deriving DecidableEq

instance : Fintype DblK :=
  Fintype.ofList [.I, .B, .O] (fun x => by cases x <;> simp)

inductive DblL
  | start | outer | dbl | back
  deriving DecidableEq

instance : Fintype DblL :=
  Fintype.ofList [.start, .outer, .dbl, .back] (fun x => by cases x <;> simp)

abbrev DblΓ : DblK → Type := fun _ => Bool

def dblProg : DblL → TM2.Stmt DblΓ DblL (Option Bool)
  | .start => .push .O (fun _ => true) (.goto fun _ => .outer)
  | .outer =>
    .pop .I (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => .dbl)
        .halt)
  | .dbl =>
    .pop .O (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .B (fun _ => true) (.push .B (fun _ => true) (.goto fun _ => .dbl)))
        (.goto fun _ => .back))
  | .back =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .O (fun _ => true) (.goto fun _ => .back))
        (.goto fun _ => .outer))

def dblTM : FinTM2 where
  K := DblK
  k₀ := .I
  k₁ := .O
  Γ := DblΓ
  Λ := DblL
  main := .start
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := dblProg

def dstk (i b o : List Bool) : ∀ k, List (DblΓ k)
  | .I => i
  | .B => b
  | .O => o

@[simp] theorem dstk_set_I (i i' b o : List Bool) :
    Function.update (dstk i b o) .I i' = dstk i' b o := by
  funext k; cases k <;> simp [dstk]
@[simp] theorem dstk_set_B (i b b' o : List Bool) :
    Function.update (dstk i b o) .B b' = dstk i b' o := by
  funext k; cases k <;> simp [dstk]
@[simp] theorem dstk_set_O (i b o o' : List Bool) :
    Function.update (dstk i b o) .O o' = dstk i b o' := by
  funext k; cases k <;> simp [dstk]

theorem dstk_start (i : List Bool) :
    dstk i [] [] = Function.update (fun _ => [] : ∀ k, List (DblΓ k)) .I i := by
  funext k; cases k <;> simp [dstk]

theorem dstk_end (o : List Bool) :
    dstk [] [] o = Function.update (fun _ => [] : ∀ k, List (DblΓ k)) .O o := by
  funext k; cases k <;> simp [dstk]

abbrev DblCfg : Type := TM2.Cfg DblΓ DblL (Option Bool)

abbrev dblStep : Option DblCfg → Option DblCfg := flip bind (TM2.step dblProg)

theorem d_start (s : Option Bool) (i b o : List Bool) :
    dblStep (some ⟨some .start, s, dstk i b o⟩) =
      some ⟨some .outer, s, dstk i b (true :: o)⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_outer_cons (s : Option Bool) (y : Bool) (i b o : List Bool) :
    dblStep (some ⟨some .outer, s, dstk (y :: i) b o⟩) =
      some ⟨some .dbl, some y, dstk i b o⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_outer_nil (s : Option Bool) (b o : List Bool) :
    dblStep (some ⟨some .outer, s, dstk [] b o⟩) =
      some ⟨none, none, dstk [] b o⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_dbl_cons (s : Option Bool) (y : Bool) (i b o : List Bool) :
    dblStep (some ⟨some .dbl, s, dstk i b (y :: o)⟩) =
      some ⟨some .dbl, some y, dstk i (true :: true :: b) o⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_dbl_nil (s : Option Bool) (i b : List Bool) :
    dblStep (some ⟨some .dbl, s, dstk i b []⟩) =
      some ⟨some .back, none, dstk i b []⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_back_cons (s : Option Bool) (y : Bool) (i b o : List Bool) :
    dblStep (some ⟨some .back, s, dstk i (y :: b) o⟩) =
      some ⟨some .back, some y, dstk i b (true :: o)⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_back_nil (s : Option Bool) (i o : List Bool) :
    dblStep (some ⟨some .back, s, dstk i [] o⟩) =
      some ⟨some .outer, none, dstk i [] o⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

abbrev drep (n : ℕ) : List Bool := List.replicate n true

theorem drep_succ (n : ℕ) : true :: drep n = drep (n + 1) := rfl

theorem dblLoop (i : List Bool) :
    ∀ (L b : ℕ) (s : Option Bool),
      dblStep^[L + 1] (some ⟨some .dbl, s, dstk i (drep b) (drep L)⟩) =
        some ⟨some .back, none, dstk i (drep (2 * L + b)) []⟩ := by
  intro L
  induction L with
  | zero => intro b s; simpa using d_dbl_nil s i (drep b)
  | succ L ih =>
    intro b s
    rw [Function.iterate_succ_apply, ← drep_succ L, d_dbl_cons, drep_succ, drep_succ, ih]
    rw [show 2 * L + (b + 1 + 1) = 2 * (L + 1) + b from by omega]

theorem backLoop (i : List Bool) :
    ∀ (c o : ℕ) (s : Option Bool),
      dblStep^[c + 1] (some ⟨some .back, s, dstk i (drep c) (drep o)⟩) =
        some ⟨some .outer, none, dstk i [] (drep (c + o))⟩ := by
  intro c
  induction c with
  | zero => intro o s; simpa using d_back_nil s i (drep o)
  | succ c ih =>
    intro o s
    rw [Function.iterate_succ_apply, ← drep_succ c, d_back_cons, drep_succ, ih]
    rw [show c + (o + 1) = c + 1 + o from by omega]

def osteps : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, L => osteps m (2 * L) + ((2 * L + 1) + ((L + 1) + 1))

theorem osteps_eq : ∀ m L, osteps m L + 3 * L = 3 * 2 ^ m * L + 3 * m + 1 := by
  intro m
  induction m with
  | zero => intro L; simp [osteps]; ring
  | succ m ih =>
    intro L
    have h := ih (2 * L)
    simp only [osteps]
    rw [pow_succ]
    nlinarith [h]

theorem outerLoop : ∀ (i : List Bool) (L : ℕ) (s : Option Bool),
    dblStep^[osteps i.length L] (some ⟨some .outer, s, dstk i [] (drep L)⟩) =
      some ⟨none, none, dstk [] [] (drep (2 ^ i.length * L))⟩ := by
  intro i
  induction i with
  | nil => intro L s; simpa [osteps] using d_outer_nil s [] (drep L)
  | cons y i ih =>
    intro L s
    rw [List.length_cons, osteps, Function.iterate_add_apply,
      Function.iterate_add_apply dblStep (2 * L + 1),
      Function.iterate_succ_apply dblStep (L + 1), d_outer_cons]
    have h1 : dblStep^[L + 1] (some ⟨some .dbl, some y, dstk i (drep 0) (drep L)⟩) =
        some ⟨some .back, none, dstk i (drep (2 * L + 0)) []⟩ := dblLoop i L 0 (some y)
    simp only [drep, List.replicate_zero, Nat.add_zero] at h1
    rw [h1]
    have h2 : dblStep^[2 * L + 1]
        (some ⟨some .back, none, dstk i (drep (2 * L)) (drep 0)⟩) =
        some ⟨some .outer, none, dstk i [] (drep (2 * L + 0))⟩ := backLoop i (2 * L) 0 none
    simp only [drep, List.replicate_zero, Nat.add_zero] at h2
    rw [h2]
    have h3 := ih (2 * L) none
    simp only [drep] at h3
    rw [show 2 ^ (i.length + 1) * L = 2 ^ i.length * (2 * L) by ring]
    exact h3

theorem dbl_run (x : List Bool) :
    (flip bind (TM2.step dblProg))^[osteps x.length 1 + 1]
        (some (initList dblTM x)) =
      some (haltList dblTM (drep (2 ^ x.length))) := by
  refine (congrArg (fun c => (flip bind (TM2.step dblProg))^[osteps x.length 1 + 1]
    (some c)) (initList_eq dblTM _)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq dblTM _)).symm)
  show dblStep^[osteps x.length 1 + 1]
    (some (⟨some .start, none, Function.update (fun _ => []) .I x⟩ : DblCfg)) =
    some (⟨none, none, Function.update (fun _ => []) .O (drep (2 ^ x.length))⟩ : DblCfg)
  rw [← dstk_start, ← dstk_end, Function.iterate_succ_apply, d_start]
  have h := outerLoop x 1 none
  simp only [Nat.mul_one] at h
  exact h

def dblTime (m : ℕ) : ℕ := 3 * 2 ^ m + 3 * m

theorem dblTime_mono : Monotone dblTime := by
  intro a b h
  unfold dblTime
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
  omega

theorem dbl_time :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (2 ^ x.length) true) dblTime := by
  refine ⟨{
    tm := dblTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := dblTime
    outputsFun := fun x =>
      { steps := osteps x.length 1 + 1
        evals_in_steps := by
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l :=
            fun l => by simp
          have := dbl_run x
          exact (congrArg (fun l => (flip bind (TM2.step dblProg))^[osteps x.length 1 + 1]
            (some (initList dblTM l))) (hm x)).trans
            (this.trans (congrArg (fun l => some (haltList dblTM l)) (hm _).symm))
        steps_le_m := by
          have := osteps_eq x.length 1
          simp only [dblTime]
          omega } }, fun _ => le_rfl⟩

/-! ## Upstream Helpers/PolyBelowExp -/

theorem pow_le_two_pow_add_const (d : ℕ) : ∃ C : ℕ, ∀ n : ℕ, n ^ d ≤ 2 ^ n + C := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num : (1 : ℝ) < 2)
  have hev := h.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N ^ d, fun n => ?_⟩
  rcases Nat.lt_or_ge n N with hn | hn
  · exact (Nat.pow_le_pow_left hn.le d).trans (Nat.le_add_left _ _)
  · have h1 := hN n hn
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    rw [div_le_one hpos] at h1
    have h2 : n ^ d ≤ 2 ^ n := by exact_mod_cast h1
    exact h2.trans (Nat.le_add_right _ _)

theorem polynomial_le_two_pow_pow_add_const (p : Polynomial ℕ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℕ, ∀ n : ℕ, p.eval n ≤ 2 ^ (n ^ k) + C := by
  obtain ⟨d, hd⟩ := PvsNP.Units.fr_ladner.PEqualNP.Library.Helpers.polynomial_le_pow_add p
  obtain ⟨C, hC⟩ := pow_le_two_pow_add_const d
  refine ⟨C + d, fun n => ?_⟩
  have h1 := hd n
  have h2 := hC n
  have h3 : 2 ^ n ≤ 2 ^ (n ^ k) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_self_pow (by omega) n)
  omega

/-! ## Upstream Helpers/PadMap -/

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

theorem sepPair_time : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
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

theorem consTrue_time : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime
    (fun x : List Bool => x)
    (fun x : List Bool => x) (fun y : List Bool => true :: y) (fun n => 2 * n + 3) :=
  fst2_time _ _ _ consδ consFin false (fun y => (cons_run_false y).symm)

/-! ## Upstream Machines/FirstTime -/

theorem clockPair_time : ∃ p : Polynomial ℕ, ∀ (t : ℕ → ℕ) (c : ℕ),
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (t x.length) true) (fun n => c * t n + c) →
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
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
          (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
            (List.replicate (t x.length) true, x))) := by
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
    have hφ : (List.map c1.outputAlphabet.invFun
        (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (x, x))).map φ =
        PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (x, x) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (x, x))]
      exact List.map_congr_left fun y _ => c1.outputAlphabet.right_inv y
    have h2 : (flip bind (TM2.step M2.m))^[n2]
        (some (initList M2 ((List.map c1.outputAlphabet.invFun
          (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (x, x))).map φ))) =
        some (haltList M2 (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
          (List.replicate (t x.length) true, x))) := by
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
              (hm _ (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
                (List.replicate (t x.length) true, x))).symm)
        steps_le_m := (Classical.choose_spec (key x)).1 } }, fun _ => le_rfl⟩

/-! ## Upstream L083 -/

theorem L083 : ∀ k : ℕ, 1 ≤ k → ∃ c : ℕ, PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime
    (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)
    (fun n : ℕ => c * 2 ^ (n ^ k) + c) := by
  intro k hk
  have h1 := clock_polyTime constList_polyTime (Polynomial.X ^ k)
  obtain ⟨p, hp⟩ := time_of_polyTime h1
  obtain ⟨C, hC⟩ := polynomial_le_two_pow_pow_add_const p k hk
  have h := comp_time (fun x : List Bool => x)
    (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => List.replicate ((Polynomial.X ^ k : Polynomial ℕ).eval x.length) true)
    (fun x : List Bool => List.replicate (2 ^ x.length) true)
    (fun n => p.eval n) dblTime (fun n => n ^ k)
    hp dbl_time dblTime_mono
    (fun a => by simp)
  simp only [List.length_replicate, Polynomial.eval_pow, Polynomial.eval_X] at h
  refine ⟨C + 10, time_mono h fun n => ?_⟩
  have e1 := hC n
  have e2 : n ^ k < 2 ^ (n ^ k) := Nat.lt_two_pow_self
  have e3 : (C + 10) * 2 ^ n ^ k = C * 2 ^ n ^ k + 10 * 2 ^ n ^ k := by ring
  simp only [dblTime]
  rw [e3]
  generalize C * 2 ^ n ^ k = D
  generalize 2 ^ n ^ k = E at *
  generalize n ^ k = N at *
  omega

/-! ## Upstream L094 -/

theorem L094 : ∀ k : ℕ, 1 ≤ k → ∃ c : ℕ, PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime
    (fun x : List Bool => x) (fun x : List Bool => x)
    (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)
    (fun n : ℕ => c * 2 ^ (n ^ k) + c) := by
  intro k hk
  have hn : ∀ n : ℕ, n ≤ 2 ^ (n ^ k) := fun n =>
    (Nat.le_self_pow (by omega) n).trans (Nat.lt_two_pow_self).le
  obtain ⟨c0, hc0⟩ := L083 k hk
  obtain ⟨p, hp⟩ := clockPair_time
  have hA := hp (fun n => 2 ^ (n ^ k)) c0 hc0
  obtain ⟨C, hC⟩ := polynomial_le_two_pow_pow_add_const p k hk
  have hB := comp_time (fun x : List Bool => x)
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun x : List Bool => x)
    (fun x : List Bool => (List.replicate (2 ^ (x.length ^ k)) true, x))
    (fun p : List Bool × List Bool => p.1 ++ false :: p.2)
    _ (fun n => 2 * n + 3) (fun n => 2 ^ (n ^ k) + n) hA
    sepPair_time (fun a b h => by dsimp; omega)
    (fun x => by simp [PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair])
  have key : ∀ j : ℕ, ∃ c : ℕ, PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime
      (fun x : List Bool => x)
      (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + j) true ++ false :: x)
      (fun n : ℕ => c * 2 ^ (n ^ k) + c) := by
    intro j
    induction j with
    | zero =>
      refine ⟨c0 + C + 20, time_mono hB fun n => ?_⟩
      have e1 := hC n
      have e2 := hn n
      have e3 : (c0 + C + 20) * 2 ^ n ^ k = c0 * 2 ^ n ^ k + C * 2 ^ n ^ k + 20 * 2 ^ n ^ k := by
        ring
      rw [e3]
      generalize c0 * 2 ^ n ^ k = D
      generalize C * 2 ^ n ^ k = D' at *
      generalize 2 ^ n ^ k = E at *
      generalize p.eval n = P at *
      omega
    | succ j ih =>
      obtain ⟨c, hc⟩ := ih
      have hS := comp_time (fun x : List Bool => x)
        (fun x : List Bool => x) (fun x : List Bool => x)
        (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + j) true ++ false :: x)
        (fun y : List Bool => true :: y)
        _ (fun n => 2 * n + 3) (fun n => 2 ^ (n ^ k) + j + 1 + n) hc
        consTrue_time (fun a b h => by dsimp; omega)
        (fun x => by simp; omega)
      refine ⟨c + 4 * j + 20, time_mono hS fun n => ?_⟩
      have e2 := hn n
      have e3 : (c + 4 * j + 20) * 2 ^ n ^ k = c * 2 ^ n ^ k + 4 * (j * 2 ^ n ^ k) +
          20 * 2 ^ n ^ k := by
        ring
      rw [e3]
      generalize c * 2 ^ n ^ k = D
      generalize j * 2 ^ n ^ k = D' at *
      generalize 2 ^ n ^ k = E at *
      omega
  exact key k

/-! ## In the campaign's definitions -/

/-- A machine with a step bound below a polynomial is a polynomial-time machine. -/
def polyOfTime {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (M : Turing.TM2ComputableInTime ea eb f) (p : Polynomial ℕ) (h : ∀ n, M.time n ≤ p.eval n) :
    Turing.TM2ComputableInPolyTime ea eb f where
  toTM2ComputableAux := M.toTM2ComputableAux
  time := p
  outputsFun := fun a => ⟨(M.outputsFun a).toEvalsTo, (M.outputsFun a).steps_le_m.trans (h _)⟩

theorem main : ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)),
    ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c := by
  intro k hk
  obtain ⟨c, M, hM⟩ := L083 k hk
  exact ⟨c, M, hM⟩

theorem main_swap : ∀ k : ℕ, 1 ≤ k → ∃ (M : Turing.TM2ComputableInTime PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)) (c : ℕ),
    ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c := by
  intro k hk
  obtain ⟨c, M, hM⟩ := main k hk
  exact ⟨M, c, hM⟩

theorem main_pos : ∀ k : ℕ, 0 < k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString
    PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)),
    ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  fun k hk => main k hk

theorem pad : ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString
    PvsNP.encodeString
      (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)),
    ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c := by
  intro k hk
  obtain ⟨c, M, hM⟩ := L094 k hk
  exact ⟨c, M, hM⟩

theorem pad_swap : ∀ k : ℕ, 1 ≤ k → ∃ (M : Turing.TM2ComputableInTime PvsNP.encodeString
    PvsNP.encodeString
      (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)) (c : ℕ),
    ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c := by
  intro k hk
  obtain ⟨c, M, hM⟩ := pad k hk
  exact ⟨M, c, hM⟩

theorem pad_pos : ∀ k : ℕ, 0 < k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString
    PvsNP.encodeString
      (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)),
    ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  fun k hk => pad k hk

/-- The doubling clock `x ↦ 1 ^ (2 ^ |x|)` within `c * 2 ^ n + c` steps. -/
theorem exp1 : ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
    (fun x : List Bool => List.replicate (2 ^ x.length) true)), ∀ n : ℕ, M.time n ≤ c * 2 ^ n + c := by
  obtain ⟨M, hM⟩ := dbl_time
  refine ⟨6, M, fun n => (hM n).trans ?_⟩
  have e : n < 2 ^ n := Nat.lt_two_pow_self
  simp only [dblTime]
  omega



theorem h_ex2 :
    ∀ k : ℕ, 1 ≤ k → ∃ c : ℕ, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true), ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.main


theorem h_n :
    ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)), ∀ n, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.main


theorem h_h :
    ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)), ∀ n, h.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.main


theorem h_hN :
    ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)), ∀ n : ℕ, h.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.main


theorem h_ex2h :
    ∀ k : ℕ, 1 ≤ k → ∃ c : ℕ, ∃ h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true), ∀ n, h.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.main


theorem h_hc :
    ∀ k : ℕ, 1 ≤ k → ∃ (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)) (c : ℕ), ∀ n, h.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.main_swap


theorem h_Mc :
    ∀ k : ℕ, 1 ≤ k → ∃ (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)) (c : ℕ), ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.main_swap


theorem h_pos :
    ∀ k : ℕ, 0 < k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)), ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.main_pos


theorem h_pad :
    ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)), ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.pad


theorem h_pad_ex2 :
    ∀ k : ℕ, 1 ≤ k → ∃ c : ℕ, ∃ M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x), ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.pad


theorem h_pad_n :
    ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)), ∀ n, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.pad


theorem h_pad_h :
    ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)), ∀ n, h.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.pad


theorem h_pad_hN :
    ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)), ∀ n : ℕ, h.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.pad


theorem h_pad_ex2h :
    ∀ k : ℕ, 1 ≤ k → ∃ c : ℕ, ∃ h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x), ∀ n, h.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.pad


theorem h_pad_hc :
    ∀ k : ℕ, 1 ≤ k → ∃ (h : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)) (c : ℕ), ∀ n, h.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.pad_swap


theorem h_pad_Mc :
    ∀ k : ℕ, 1 ≤ k → ∃ (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)) (c : ℕ), ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.pad_swap


theorem h_pad_pos :
    ∀ k : ℕ, 0 < k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)), ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.pad_pos


theorem h_exp1 :
    ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString (fun x : List Bool => List.replicate (2 ^ x.length) true)), ∀ n : ℕ, M.time n ≤ c * 2 ^ n + c :=
  PvsNP.Units.m2_padded_exp_clock.exp1


end PvsNP.Units.m2_padded_exp_clock

theorem PvsNP.Units.m2_padded_exp_clock :
    ∀ k : ℕ, 1 ≤ k → ∃ (c : ℕ) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeString
        (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)),
      ∀ n : ℕ, M.time n ≤ c * 2 ^ (n ^ k) + c :=
  PvsNP.Units.m2_padded_exp_clock.h_pad
