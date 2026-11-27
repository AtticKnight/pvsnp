import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_upward_padding
import PvsNP.Units.m2_p_union
import PvsNP.Units.m2_exp_compl

/-
Adapted from github.com/open-goat/pequalnp-proofs (formerly brilliant-hq/pequalnp-proofs) at commit
8df87a862bd9a618faecf10ba65bff72706442c9, licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0), from its files
  lean/PEqualNP/Library/Helpers/ExpDoubling.lean (the doubling machine, dbl_time),
  lean/PEqualNP/Library/Helpers/PolyBelowExp.lean (polynomial_le_two_pow_pow_add_const),
  lean/PEqualNP/Library/Helpers/PadMap.lean (fst2_time, sepPair_time, consTrue_time),
  lean/PEqualNP/Library/Machines/FirstTime.lean (clockPair_time),
  lean/PEqualNP/Library/L083.lean, lean/PEqualNP/Library/L094.lean,
  lean/PEqualNP/Library/Helpers/ExpBound.lean (ExpBound and its closure lemmas),
  lean/PEqualNP/Library/Helpers/FirstTimeGen.lean (first_time) and
  lean/PEqualNP/Library/Helpers/PadTest.lean (padTest).
MODIFIED from those files: joined here in that order inside the namespace of this unit, on top of the settled
campaign unit fr_ladner (github.com/makedotfun/pvsnp, PvsNP/Units/fr_ladner.lean, imported), in whose namespace the
upstream Defs and Library machines live (upstream PEqualNP.Library.X is PvsNP.Units.fr_ladner.PEqualNP.Library.X here,
written with that full name); a reducible def is an abbrev. This block is copied from our verified file
m2_padded_test_exp.lean (same upstream sources). New here: the padding argument for EXP closure under union (then intersection by complements, settled unit m2_exp_compl), via
the settled campaign units m2_upward_padding (a padded EXP language is in P) and m2_p_union (P is closed under union).
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_exp_inter

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


/-! ## Upstream Helpers/ExpBound -/

/-- `f` is below `2 ^ (A * (n + 1) ^ D)` for some `A`, `D`. -/
def ExpBound (f : ℕ → ℕ) : Prop := ∃ A D : ℕ, ∀ n, f n ≤ 2 ^ (A * (n + 1) ^ D)

theorem eb_mono {f g : ℕ → ℕ} (h : ∀ n, f n ≤ g n) (hg : ExpBound g) : ExpBound f := by
  obtain ⟨A, D, hA⟩ := hg
  exact ⟨A, D, fun n => (h n).trans (hA n)⟩

theorem eb_const (c : ℕ) : ExpBound (fun _ => c) :=
  ⟨c, 0, fun n => by simpa using (Nat.lt_two_pow_self (n := c)).le⟩

theorem exp_le_merge (A B D E n : ℕ) :
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
  obtain ⟨s, hs⟩ := PvsNP.Units.fr_ladner.PEqualNP.Library.Helpers.polynomial_le_pow_add p
  obtain ⟨A, D, hA⟩ := hf
  have h : ExpBound (fun n => (2 ^ (A * (n + 1) ^ D)) ^ s + s) := by
    refine eb_add ⟨A * s, D, fun n => ?_⟩ (eb_const s)
    show (2 ^ (A * (n + 1) ^ D)) ^ s ≤ _
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [mul_right_comm])
  exact eb_mono (fun n => (PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.eval_mono p (hA n)).trans
    (hs _)) h

/-- Every member is below `2 ^ (n ^ j) + j` for some `j`. -/
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

/-! ## Upstream Helpers/FirstTimeGen -/

theorem first_time (f : List Bool → List Bool) (t len : ℕ → ℕ) (ht : Monotone t)
    (hl : Monotone len) (hlen : ∀ x, (f x).length ≤ len x.length)
    (h : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      (fun x : List Bool => x) f t) :
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      (fun p : List Bool × List Bool => (f p.1, p.2)) (fun n => t n + 2 * n + 2 * len n + 5) := by
  obtain ⟨c, hc⟩ := h
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let T : ℕ → ℕ := fun n => t n + 2 * n + 2 * len n + 5
  have key : ∀ p : List Bool × List Bool, ∃ n, n ≤ T (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair p).length ∧
      (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁)
          (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (f p.1, p.2))) := by
    rintro ⟨x, w⟩
    have hs : ∃ s, s ≤ c.time x.length ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps, (c.outputsFun x).steps_le_m, (c.outputsFun x).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run e₀ e₁ x w _ s h
    have hm : (List.map c.outputAlphabet.invFun (f x)).map e₁ = f x := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have b2 : c.time x.length ≤ t (x.length + w.length) :=
      (hc _).trans (ht (by omega))
    have b3 : (f x).length ≤ len (x.length + w.length) :=
      (hlen x).trans (hl (by omega))
    simp only [T, encodePair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair p))).trans
            ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm e₀ e₁) l))
              (hm _ (PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (f p.1, p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }, fun _ => le_rfl⟩

/-! ## Upstream Helpers/PadTest -/

/-- Transducer writing one extra `false` in front. -/
def consFδ : Bool → Bool → Bool × Option Bool × Option Bool
  | false, b => (true, some false, some b)
  | true, b => (true, some b, none)

/-- End of input: write the extra `false` if it was not written. -/
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

theorem consFalse_time : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
    (fun x : List Bool => x) (fun y : List Bool => false :: y) (fun n => 2 * n + 3) :=
  fst2_time _ _ _ consFδ consFFin false (fun y => (consF_run_false y).symm)

/-- The padding for `k = 0` is `x ↦ 1 1 0 x`, linear time. -/
theorem pad0_time : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
    (fun x : List Bool => x) (fun x : List Bool => true :: true :: false :: x)
    (fun n => 30 * 2 ^ n + 30) := by
  have h2 := comp_time (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => x)
    (fun y : List Bool => false :: y) (fun y : List Bool => true :: y)
    _ (fun n => 2 * n + 3) (fun n => n + 1) consFalse_time consTrue_time
    (fun a b h => by dsimp; omega) (fun x => by simp)
  have h3 := comp_time (fun x : List Bool => x) (fun x : List Bool => x) (fun x : List Bool => x)
    (fun y : List Bool => true :: false :: y) (fun y : List Bool => true :: y)
    _ (fun n => 2 * n + 3) (fun n => n + 2) h2 consTrue_time
    (fun a b h => by dsimp; omega) (fun x => by simp)
  refine time_mono h3 fun n => ?_
  have : n < 2 ^ n := Nat.lt_two_pow_self
  omega

/-- The padding map, for every `k`, with a time bound `c * 2 ^ (n ^ K) + c` (`K ≥ 1`) and an
output length bound. -/
theorem pad_time_gen (k : ℕ) : ∃ c K : ℕ, 1 ≤ K ∧
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)
      (fun n : ℕ => c * 2 ^ (n ^ K) + c) ∧
    ∀ x : List Bool, (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x).length ≤
      2 * 2 ^ (x.length ^ K) + k + 1 + x.length := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨30, 1, le_rfl, ?_, fun x => ?_⟩
    · have e : (fun x : List Bool => List.replicate (2 ^ (x.length ^ 0) + 0) true ++ false :: x) =
          fun x : List Bool => true :: true :: false :: x := by
        funext x; simp [List.replicate]
      rw [e]
      simpa using pad0_time
    · have : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
      simp
      omega
  · obtain ⟨c, hc⟩ := L094 k hk
    refine ⟨c, k, hk, hc, fun x => ?_⟩
    simp
    omega

theorem two_pow_pow_mono (K : ℕ) : Monotone (fun n : ℕ => 2 ^ (n ^ K)) :=
  fun _ _ h => Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left h K)

theorem padTest : ∀ (k : ℕ) (u v : List Bool → List Bool) (h : List Bool × List Bool → Bool),
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) u →
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) v →
    PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
      Computability.encodeBool h →
    ∃ j : ℕ, PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInTime (fun x : List Bool => x) Computability.encodeBool
      (fun z : List Bool => h (List.replicate (2 ^ ((u z).length ^ k) + k) true ++ false :: u z,
        v z)) (fun n : ℕ => 2 ^ (n ^ j) + j) := by
  intro k u v h hu hv hh
  obtain ⟨c, K, hK, hpad, hpadlen⟩ := pad_time_gen k
  obtain ⟨a, d, had⟩ := PvsNP.Units.fr_ladner.PEqualNP.Library.Helpers.output_length_le u hu
  obtain ⟨b, e, hbe⟩ := PvsNP.Units.fr_ladner.PEqualNP.Library.Helpers.output_length_le v hv
  -- the lengths of `u z` and `v z` are below a monomial in `|z| + 1`
  let A := a + (u []).length + b + (v []).length + 1
  let D := d + e
  have hU : ∀ z : List Bool, (u z).length + (v z).length ≤ A * (z.length + 1) ^ D := by
    intro z
    have h1 : 1 ≤ (z.length + 1) ^ D := Nat.one_le_pow _ _ (by omega)
    rcases Nat.eq_zero_or_pos z.length with h0 | h0
    · rw [List.length_eq_zero_iff.mp h0]
      simp only [List.length_nil, zero_add, one_pow, mul_one, A]
      omega
    · have hd : z.length ^ d ≤ (z.length + 1) ^ D :=
        (Nat.pow_le_pow_left (by omega) d).trans (Nat.pow_le_pow_right (by omega) (by omega))
      have he : z.length ^ e ≤ (z.length + 1) ^ D :=
        (Nat.pow_le_pow_left (by omega) e).trans (Nat.pow_le_pow_right (by omega) (by omega))
      have e1 := (had z h0).trans (Nat.mul_le_mul_left a hd)
      have e2 := (hbe z h0).trans (Nat.mul_le_mul_left b he)
      have e3 : A * (z.length + 1) ^ D = a * (z.length + 1) ^ D + b * (z.length + 1) ^ D +
          ((u []).length + (v []).length + 1) * (z.length + 1) ^ D := by
        simp only [A]; ring
      have e4 : (u []).length + (v []).length + 1 ≤
          ((u []).length + (v []).length + 1) * (z.length + 1) ^ D := Nat.le_mul_of_pos_right _ h1
      omega
  let ℓ : ℕ → ℕ := fun n => A * (n + 1) ^ D
  have hℓ : Monotone ℓ := fun x y hxy =>
    Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega) D)
  -- step 1: the pair
  obtain ⟨p1, h1⟩ := time_of_polyTime (cpt_pair hu hv)
  -- step 2: padding the first component
  let len2 : ℕ → ℕ := fun n => 2 * 2 ^ (n ^ K) + k + 1 + n
  have hlen2 : Monotone len2 := fun x y hxy => by
    have : 2 ^ (x ^ K) ≤ 2 ^ (y ^ K) := two_pow_pow_mono K hxy
    simp only [len2]; omega
  let t2 : ℕ → ℕ := fun n => c * 2 ^ (n ^ K) + c
  have ht2 : Monotone t2 := fun x y hxy => by
    have : c * 2 ^ (x ^ K) ≤ c * 2 ^ (y ^ K) := Nat.mul_le_mul_left c (two_pow_pow_mono K hxy)
    simp only [t2]; omega
  have h2 := first_time
    (fun x : List Bool => List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x)
    t2 len2 ht2 hlen2 hpadlen hpad
  have hmono2 : Monotone (fun n => t2 n + 2 * n + 2 * len2 n + 5) := fun x y hxy => by
    have := ht2 hxy
    have := hlen2 hxy
    dsimp only; omega
  have h12 := comp_time (fun x : List Bool => x) PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
    PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair (fun z : List Bool => (u z, v z))
    (fun p : List Bool × List Bool =>
      (List.replicate (2 ^ (p.1.length ^ k) + k) true ++ false :: p.1, p.2))
    _ _ ℓ h1 h2 hmono2 (fun z => by rw [encodePair_length]; exact hU z)
  -- step 3: the test
  obtain ⟨ph, h3⟩ := time_of_polyTime hh
  have h123 := comp_time (fun x : List Bool => x) PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair
    Computability.encodeBool
    (fun z : List Bool => (List.replicate (2 ^ ((u z).length ^ k) + k) true ++ false :: u z, v z))
    h _ (fun n => ph.eval n) (fun n => len2 (ℓ n)) h12 h3
    (fun _ _ hxy => eval_mono ph hxy) (fun z => by
      rw [encodePair_length]
      have e1 := hpadlen (u z)
      have e2 : (u z).length + (v z).length ≤ ℓ z.length := hU z
      have e3 : 2 ^ ((u z).length ^ K) ≤ 2 ^ ((ℓ z.length) ^ K) := two_pow_pow_mono K (by omega)
      simp only [len2] at e1 ⊢
      omega)
  -- the arithmetic
  have hEℓ : ExpBound ℓ := eb_of_le_monomial A D (fun n => le_rfl)
  have hEG : ExpBound (fun n => 2 ^ (ℓ n ^ K)) := eb_two_pow A D K (fun n => le_rfl)
  have hEL : ExpBound (fun n => len2 (ℓ n)) :=
    eb_add (eb_add (eb_mul (eb_const 2) hEG) (eb_const (k + 1))) hEℓ |> eb_mono (fun n => by
      simp only [len2]; omega)
  have hEt2 : ExpBound (fun n => t2 (ℓ n)) :=
    eb_add (eb_mul (eb_const c) hEG) (eb_const c)
  have hE1 : ExpBound (fun n => p1.eval n) := eb_poly p1 eb_id
  have hE3 : ExpBound (fun n => ph.eval (len2 (ℓ n))) := eb_poly ph hEL
  have hEall : ExpBound (fun n => p1.eval n + (2 * ℓ n + 2) + (t2 (ℓ n) + 2 * ℓ n +
      2 * len2 (ℓ n) + 5) + (2 * len2 (ℓ n) + 2) + ph.eval (len2 (ℓ n))) := by
    have hlin : ExpBound (fun n => 5 * ℓ n + 4 * len2 (ℓ n) + 9) :=
      eb_add (eb_add (eb_mul (eb_const 5) hEℓ) (eb_mul (eb_const 4) hEL)) (eb_const 9)
    exact eb_mono (fun n => by omega) (eb_add (eb_add (eb_add hE1 hlin) hEt2) hE3)
  obtain ⟨j, hj⟩ := eb_final hEall
  exact ⟨j, time_mono h123 hj⟩


/-! ## Padding facts -/

theorem rep_inj : ∀ (t1 t2 : ℕ) (x y : List Bool),
    List.replicate t1 true ++ false :: x = List.replicate t2 true ++ false :: y → t1 = t2 ∧ x = y := by
  intro t1
  induction t1 with
  | zero =>
    intro t2 x y h
    cases t2 with
    | zero =>
      simp only [List.replicate_zero, List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨rfl, h⟩
    | succ t2 => simp [List.replicate_succ] at h
  | succ t1 ih =>
    intro t2 x y h
    cases t2 with
    | zero => simp [List.replicate_succ] at h
    | succ t2 =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih t2 x y h
      exact ⟨by omega, h2⟩

/-- A language whose padded version is decided in polynomial time is decided in exponential time. -/
theorem exp_of_padded (L : Language Bool) (k : ℕ) (h : List Bool → Bool)
    (hh : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer h)
    (hL : ∀ x : List Bool, x ∈ L ↔ h (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = true) :
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  have hh' : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      Computability.encodeBool h := hh
  have hfst : PvsNP.Units.fr_ladner.PEqualNP.Library.ComputableInPolyTime
      PvsNP.Units.fr_ladner.PEqualNP.Library.encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => h p.1) :=
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
      PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_fst hh'
  obtain ⟨j, M, hM⟩ := padTest k (fun x : List Bool => x) (fun _ : List Bool => ([] : List Bool))
    (fun p : List Bool × List Bool => h p.1)
    PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_id
    (PvsNP.Units.fr_ladner.PEqualNP.Library.Universal.cpt_const []) hfst
  exact ⟨j, _, M, hL, hM⟩

theorem lift_bound (a k n : ℕ) (ha : a < k) : 2 ^ (n ^ a) + a ≤ 2 ^ (n ^ k) + k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (0 : ℕ) ^ a ≤ 1 := by
      rcases a with _ | a
      · simp
      · simp
    have h1 : (0 : ℕ) ^ k = 0 := zero_pow (by omega)
    have h2 : 2 ^ ((0 : ℕ) ^ a) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h0
    rw [h1]
    simp only [pow_zero, pow_one] at h2 ⊢
    omega
  · have h1 : n ^ a ≤ n ^ k := Nat.pow_le_pow_right hn (le_of_lt ha)
    have h2 : 2 ^ (n ^ a) ≤ 2 ^ (n ^ k) := Nat.pow_le_pow_right (by norm_num) h1
    omega

theorem main : ∀ L₁ L₂ : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L₁ ⊔ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  rintro L₁ L₂ ⟨k₁, f₁, M₁, hf₁, ht₁⟩ ⟨k₂, f₂, M₂, hf₂, ht₂⟩
  have hP1 := PvsNP.Units.m2_upward_padding L₁ (k₁ + k₂ + 1)
    ⟨f₁, M₁, hf₁, fun n => (ht₁ n).trans (lift_bound k₁ (k₁ + k₂ + 1) n (by omega))⟩
  have hP2 := PvsNP.Units.m2_upward_padding L₂ (k₁ + k₂ + 1)
    ⟨f₂, M₂, hf₂, fun n => (ht₂ n).trans (lift_bound k₂ (k₁ + k₂ + 1) n (by omega))⟩
  obtain ⟨h, hh, hmem⟩ := PvsNP.Units.m2_p_union _ _ hP1 hP2
  refine exp_of_padded (L₁ ⊔ L₂) (k₁ + k₂ + 1) h hh (fun x => ?_)
  rw [← hmem]
  change (x ∈ L₁ ∨ x ∈ L₂) ↔
    ((∃ y : List Bool, y ∈ L₁ ∧
        List.replicate (2 ^ (x.length ^ (k₁ + k₂ + 1)) + (k₁ + k₂ + 1)) true ++ false :: x =
          List.replicate (2 ^ (y.length ^ (k₁ + k₂ + 1)) + (k₁ + k₂ + 1)) true ++ false :: y) ∨
      (∃ y : List Bool, y ∈ L₂ ∧
        List.replicate (2 ^ (x.length ^ (k₁ + k₂ + 1)) + (k₁ + k₂ + 1)) true ++ false :: x =
          List.replicate (2 ^ (y.length ^ (k₁ + k₂ + 1)) + (k₁ + k₂ + 1)) true ++ false :: y))
  constructor
  · rintro (hx | hx)
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨y, hy, he⟩ | ⟨y, hy, he⟩)
    · obtain ⟨_, rfl⟩ := rep_inj _ _ _ _ he
      exact Or.inl hy
    · obtain ⟨_, rfl⟩ := rep_inj _ _ _ _ he
      exact Or.inr hy


theorem inter_main : ∀ L₁ L₂ : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ⊓ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L₁ L₂ h₁ h₂
  have c₁ := PvsNP.Units.m2_exp_compl L₁ h₁
  have c₂ := PvsNP.Units.m2_exp_compl L₂ h₂
  have u := main L₁ᶜ L₂ᶜ c₁ c₂
  obtain ⟨k, f, M, hf, hM⟩ := PvsNP.Units.m2_exp_compl (L₁ᶜ ⊔ L₂ᶜ) u
  refine ⟨k, f, M, fun x => ?_, hM⟩
  rw [← hf x]
  change (x ∈ L₁ ∧ x ∈ L₂) ↔ ¬ (¬ x ∈ L₁ ∨ ¬ x ∈ L₂)
  tauto

theorem diff_main : ∀ L₁ L₂ : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ ({x : List Bool | x ∈ L₁ ∧ x ∉ L₂} : Language Bool) ↔ f x = true) ∧
          ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L₁ L₂ h₁ h₂
  obtain ⟨k, f, M, hf, hM⟩ := inter_main L₁ L₂ᶜ h₁ (PvsNP.Units.m2_exp_compl L₂ h₂)
  exact ⟨k, f, M, fun x => hf x, hM⟩

theorem set_main : ∀ L₁ L₂ : Language Bool,
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ ({x : List Bool | x ∈ L₁ ∧ x ∈ L₂} : Language Bool) ↔ f x = true) ∧
          ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L₁ L₂ h₁ h₂
  obtain ⟨k, f, M, hf, hM⟩ := inter_main L₁ L₂ h₁ h₂
  exact ⟨k, f, M, fun x => hf x, hM⟩



theorem h_set : ∀ L₁ L₂ : Language Bool, (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) → (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) → ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ ({x : List Bool | x ∈ L₁ ∧ x ∈ L₂} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := PvsNP.Units.m2_exp_inter.set_main


theorem h_diff : ∀ L₁ L₂ : Language Bool, (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) → (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) → ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f), (∀ x : List Bool, x ∈ ({x : List Bool | x ∈ L₁ ∧ x ∉ L₂} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := PvsNP.Units.m2_exp_inter.diff_main


end PvsNP.Units.m2_exp_inter

theorem PvsNP.Units.m2_exp_inter :
    ∀ L₁ L₂ : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L₁ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L₁ ⊓ L₂ ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.m2_exp_inter.inter_main
