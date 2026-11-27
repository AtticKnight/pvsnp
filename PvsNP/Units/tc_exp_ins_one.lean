import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.tc_exp_ins_one

open Turing

theorem eval_le_eval_one_mul_pow (p : Polynomial ℕ) {n : ℕ} (hn : 1 ≤ n) :
    p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun e he => ?_
  have hed : e ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp e he
  have hpow : n ^ e ≤ n ^ p.natDegree := Nat.pow_le_pow_right hn hed
  simp only [one_pow, mul_one]
  exact Nat.mul_le_mul_left (p.coeff e) hpow

theorem exp_poly_bound (p : Polynomial ℕ) :
    ∃ K : ℕ, ∀ n : ℕ, 2 ^ p.eval n ≤ 2 ^ (n ^ K) + K := by
  let K : ℕ := 2 ^ p.eval 0 + 2 ^ p.eval 1 + p.natDegree
  refine ⟨K, fun n => ?_⟩
  match n with
  | 0 =>
    have h0 : 2 ^ p.eval 0 ≤ K :=
      (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    exact h0.trans (Nat.le_add_left K _)
  | 1 =>
    have h1 : 2 ^ p.eval 1 ≤ K :=
      (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    exact h1.trans (Nat.le_add_left K _)
  | m + 2 =>
    have hge1 : 1 ≤ m + 2 := by omega
    have hge2 : 2 ≤ m + 2 := by omega
    have h1 : p.eval (m + 2) ≤ p.eval 1 * (m + 2) ^ p.natDegree :=
      eval_le_eval_one_mul_pow p hge1
    have h2 : p.eval 1 ≤ 2 ^ p.eval 1 := Nat.le_of_lt Nat.lt_two_pow_self
    have h3 : 2 ^ p.eval 1 ≤ (m + 2) ^ p.eval 1 := Nat.pow_le_pow_left hge2 (p.eval 1)
    have h4 : p.eval (m + 2) ≤ (m + 2) ^ (p.eval 1 + p.natDegree) := by
      calc p.eval (m + 2)
          ≤ p.eval 1 * (m + 2) ^ p.natDegree := h1
        _ ≤ (m + 2) ^ p.eval 1 * (m + 2) ^ p.natDegree :=
            Nat.mul_le_mul_right _ (h2.trans h3)
        _ = (m + 2) ^ (p.eval 1 + p.natDegree) := (Nat.pow_add (m + 2) _ _).symm
    have hle_K : p.eval 1 + p.natDegree ≤ K :=
      Nat.add_le_add_right (h2.trans (Nat.le_add_left _ _)) p.natDegree
    have h5 : (m + 2) ^ (p.eval 1 + p.natDegree) ≤ (m + 2) ^ K :=
      Nat.pow_le_pow_right hge1 hle_K
    have h6 : 2 ^ p.eval (m + 2) ≤ 2 ^ ((m + 2) ^ K) :=
      Nat.pow_le_pow_right (by omega) (h4.trans h5)
    exact h6.trans (Nat.le_add_right _ K)

theorem ins_time_le_exp_poly (k : ℕ) :
    ∃ p : Polynomial ℕ, ∀ n : ℕ,
      n * (2 * n + 6 + (2 ^ (n ^ k) + k)) + (n + 2) ≤ 2 ^ p.eval n := by
  let p : Polynomial ℕ :=
    Polynomial.X ^ k + Polynomial.C 3 * Polynomial.X + Polynomial.C (k + 10)
  refine ⟨p, fun n => ?_⟩
  have hn1 : n + 1 ≤ 2 ^ (n + 1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hlin : 2 * n + 8 + k ≤ 2 ^ (2 * n + 8 + k) := Nat.le_of_lt Nat.lt_two_pow_self
  have h1 : 2 ^ (2 * n + 8 + k) ≤ 2 ^ (2 * n + 8 + k + n ^ k) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_add_right _ _)
  have h2 : 2 ^ (n ^ k) ≤ 2 ^ (2 * n + 8 + k + n ^ k) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _)
  have h3 : 2 * n + 8 + k + 2 ^ (n ^ k) ≤ 2 ^ (2 * n + 8 + k + n ^ k + 1) := by
    rw [Nat.pow_succ]
    have h12 := hlin.trans h1
    omega
  have htot : n * (2 * n + 6 + (2 ^ (n ^ k) + k)) + (n + 2) ≤
      (n + 1) * (2 * n + 8 + k + 2 ^ (n ^ k)) := by
    have hmul : (n + 1) * (2 * n + 8 + k + 2 ^ (n ^ k)) =
        n * (2 * n + 6 + (2 ^ (n ^ k) + k)) + ((4 * n + 8 + k) + 2 ^ (n ^ k)) := by ring
    rw [hmul]
    refine Nat.add_le_add_left ?_ _
    exact (show n + 2 ≤ 4 * n + 8 + k by omega).trans (Nat.le_add_right _ _)
  have hmul2 : (n + 1) * (2 * n + 8 + k + 2 ^ (n ^ k)) ≤
      2 ^ (n + 1) * 2 ^ (2 * n + 8 + k + n ^ k + 1) :=
    Nat.mul_le_mul hn1 h3
  have hpeval : p.eval n = (n + 1) + (2 * n + 8 + k + n ^ k + 1) := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    ring
  rw [hpeval, Nat.pow_add]
  exact htot.trans hmul2

theorem simulate_run {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (t : ℕ) (a b : σ), (flip bind f)^[t] (some a) = some b →
      (flip bind g)^[t] (some (emb a)) = some (emb b) := by
  intro t
  induction t with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; rfl
  | succ t ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab ⊢
    cases hfa : f a with
    | none =>
      have e : flip bind f (some a) = none := hfa
      rw [e] at hab
      have hnone : ∀ n : ℕ, (flip bind f)^[n] none = none := by
        intro n; induction n with | zero => rfl | succ n ihn => rw [Function.iterate_succ_apply]; exact ihn
      rw [hnone] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind f (some a) = some c := hfa
      have e' : flip bind g (some (emb a)) = some (emb c) := h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab

inductive IStk (K : Type)
  | orig (k : K) | lu | rv | tu | tv | out
  deriving DecidableEq

def iStkEquiv (K : Type) : IStk K ≃ K ⊕ Fin 5 where
  toFun
    | .orig k => Sum.inl k
    | .lu => Sum.inr 0
    | .rv => Sum.inr 1
    | .tu => Sum.inr 2
    | .tv => Sum.inr 3
    | .out => Sum.inr 4
  invFun
    | Sum.inl k => .orig k
    | Sum.inr ⟨0, _⟩ => .lu
    | Sum.inr ⟨1, _⟩ => .rv
    | Sum.inr ⟨2, _⟩ => .tu
    | Sum.inr ⟨3, _⟩ => .tv
    | Sum.inr ⟨4, _⟩ => .out
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with k | i
    · rfl
    · fin_cases i <;> rfl

instance instFintypeIStk (K : Type) [Fintype K] : Fintype (IStk K) :=
  Fintype.ofEquiv (K ⊕ Fin 5) (iStkEquiv K).symm

inductive ILbl (Λ : Type)
  | orig (l : Λ)
  | next | revV | loadV | loadU | restoreU | afterM | drainLU
  deriving DecidableEq

def iLblEquiv (Λ : Type) : ILbl Λ ≃ Λ ⊕ Fin 7 where
  toFun
    | .orig l => Sum.inl l
    | .next => Sum.inr 0
    | .revV => Sum.inr 1
    | .loadV => Sum.inr 2
    | .loadU => Sum.inr 3
    | .restoreU => Sum.inr 4
    | .afterM => Sum.inr 5
    | .drainLU => Sum.inr 6
  invFun
    | Sum.inl l => .orig l
    | Sum.inr ⟨0, _⟩ => .next
    | Sum.inr ⟨1, _⟩ => .revV
    | Sum.inr ⟨2, _⟩ => .loadV
    | Sum.inr ⟨3, _⟩ => .loadU
    | Sum.inr ⟨4, _⟩ => .restoreU
    | Sum.inr ⟨5, _⟩ => .afterM
    | Sum.inr ⟨6, _⟩ => .drainLU
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with l | i
    · rfl
    · fin_cases i <;> rfl

instance instFintypeILbl (Λ : Type) [Fintype Λ] : Fintype (ILbl Λ) :=
  Fintype.ofEquiv (Λ ⊕ Fin 7) (iLblEquiv Λ).symm

abbrev IΓ (M : FinTM2) : IStk M.K → Type
  | .orig k => M.Γ k
  | _ => Bool

abbrev Iσ (M : FinTM2) : Type := M.σ × Bool × Bool × Option Bool

def initσ (M : FinTM2) : Iσ M := (M.initialState, false, false, none)

def trM {M : FinTM2} : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (IΓ M) (ILbl M.Λ) (Iσ M)
  | .push k f q => .push (.orig k) (fun st => f st.1) (trM q)
  | .peek k f q => .peek (.orig k) (fun st o => (f st.1 o, st.2)) (trM q)
  | .pop k f q => .pop (.orig k) (fun st o => (f st.1 o, st.2)) (trM q)
  | .load a q => .load (fun st => (a st.1, st.2)) (trM q)
  | .branch f q₁ q₂ => .branch (fun st => f st.1) (trM q₁) (trM q₂)
  | .goto f => .goto (fun st => .orig (f st.1))
  | .halt => .goto (fun _ => .afterM)

def iProg {f : List Bool → Bool}
    (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) :
    ILbl c.tm.Λ → TM2.Stmt (IΓ c.tm) (ILbl c.tm.Λ) (Iσ c.tm)
  | .orig l => trM (c.tm.m l)
  | .next =>
    .pop .rv (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.load (fun st => (c.tm.initialState, st.2.1, st.2.2.2.getD false, none))
          (.goto fun _ => .revV))
        (.load (fun st => (c.tm.initialState, st.2.1, false, none))
          (.goto fun _ => .drainLU)))
  | .revV =>
    .pop .rv (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.push .tv (fun st => st.2.2.2.getD false)
          (.load (fun st => (c.tm.initialState, st.2.1, st.2.2.1, none)) (.goto fun _ => .revV)))
        (.load (fun st => (c.tm.initialState, st.2.1, st.2.2.1, none)) (.goto fun _ => .loadV)))
  | .loadV =>
    .pop .tv (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.push .rv (fun st => st.2.2.2.getD false)
          (.push (.orig c.tm.k₀) (fun st => c.inputAlphabet.invFun (st.2.2.2.getD false))
            (.load (fun st => (c.tm.initialState, st.2.1, st.2.2.1, none)) (.goto fun _ => .loadV))))
        (.load (fun st => (c.tm.initialState, st.2.1, st.2.2.1, none)) (.goto fun _ => .loadU)))
  | .loadU =>
    .pop .lu (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.push .tu (fun st => st.2.2.2.getD false)
          (.push (.orig c.tm.k₀) (fun st => c.inputAlphabet.invFun (st.2.2.2.getD false))
            (.load (fun st => (c.tm.initialState, st.2.1, st.2.2.1, none)) (.goto fun _ => .loadU))))
        (.load (fun st => (c.tm.initialState, st.2.1, st.2.2.1, none)) (.goto fun _ => .restoreU)))
  | .restoreU =>
    .pop .tu (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.push .lu (fun st => st.2.2.2.getD false)
          (.load (fun st => (c.tm.initialState, st.2.1, st.2.2.1, none)) (.goto fun _ => .restoreU)))
        (.load (fun st => (c.tm.initialState, st.2.1, st.2.2.1, none))
          (.goto fun _ => .orig c.tm.main)))
  | .afterM =>
    .pop (.orig c.tm.k₁)
      (fun st o =>
        (c.tm.initialState, st.2.1 || (o.map c.outputAlphabet == some true), st.2.2.1, none))
      (.push .lu (fun st => st.2.2.1)
        (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .next)))
  | .drainLU =>
    .pop .lu (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .drainLU))
        (.push .out (fun st => st.2.1)
          (.load (fun _ => initσ c.tm) .halt)))

def insTM {f : List Bool → Bool}
    (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) : FinTM2 :=
  haveI := c.tm.kFin
  haveI := c.tm.ΛFin
  haveI := c.tm.σFin
  { K := IStk c.tm.K
    k₀ := .rv
    k₁ := .out
    Γ := IΓ c.tm
    Λ := ILbl c.tm.Λ
    main := .next
    σ := Iσ c.tm
    initialState := initσ c.tm
    m := iProg c }

abbrev ICfg (M : FinTM2) : Type := TM2.Cfg (IΓ M) (ILbl M.Λ) (Iσ M)

def mkStk {M : FinTM2} (S : ∀ k, List (M.Γ k))
    (lu rv tu tv o : List Bool) : ∀ k, List (IΓ M k)
  | .orig k => S k
  | .lu => lu
  | .rv => rv
  | .tu => tu
  | .tv => tv
  | .out => o

theorem upd_orig {M : FinTM2} (S : ∀ k, List (M.Γ k)) (k : M.K) (v : List (M.Γ k))
    (lu rv tu tv o : List Bool) :
    Function.update (mkStk S lu rv tu tv o) (.orig k) v =
      mkStk (Function.update S k v) lu rv tu tv o := by
  funext j
  cases j with
  | orig j' =>
    by_cases h : j' = k
    · subst h
      rw [Function.update_self]
      show v = Function.update S j' v j'
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j' = Function.update S k v j'
      rw [Function.update_of_ne h]
  | lu => rw [Function.update_of_ne (by simp)]; rfl
  | rv => rw [Function.update_of_ne (by simp)]; rfl
  | tu => rw [Function.update_of_ne (by simp)]; rfl
  | tv => rw [Function.update_of_ne (by simp)]; rfl
  | out => rw [Function.update_of_ne (by simp)]; rfl

theorem upd_lu {M : FinTM2} (S : ∀ k, List (M.Γ k)) (lu lu' rv tu tv o : List Bool) :
    Function.update (mkStk S lu rv tu tv o) .lu lu' = mkStk S lu' rv tu tv o := by
  funext k; cases k <;> rfl

theorem upd_rv {M : FinTM2} (S : ∀ k, List (M.Γ k)) (lu rv rv' tu tv o : List Bool) :
    Function.update (mkStk S lu rv tu tv o) .rv rv' = mkStk S lu rv' tu tv o := by
  funext k; cases k <;> rfl

theorem upd_tu {M : FinTM2} (S : ∀ k, List (M.Γ k)) (lu rv tu tu' tv o : List Bool) :
    Function.update (mkStk S lu rv tu tv o) .tu tu' = mkStk S lu rv tu' tv o := by
  funext k; cases k <;> rfl

theorem upd_tv {M : FinTM2} (S : ∀ k, List (M.Γ k)) (lu rv tu tv tv' o : List Bool) :
    Function.update (mkStk S lu rv tu tv o) .tv tv' = mkStk S lu rv tu tv' o := by
  funext k; cases k <;> rfl

theorem upd_out {M : FinTM2} (S : ∀ k, List (M.Γ k)) (lu rv tu tv o o' : List Bool) :
    Function.update (mkStk S lu rv tu tv o) .out o' = mkStk S lu rv tu tv o' := by
  funext k; cases k <;> rfl

theorem initList_insTM {f : List Bool → Bool}
    (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) (x : List Bool) :
    initList (insTM c) x = (⟨some .next, initσ c.tm, mkStk (fun _ => []) [] x [] [] []⟩ : ICfg c.tm) := by
  unfold initList
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_insTM {f : List Bool → Bool}
    (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) (o : List Bool) :
    haltList (insTM c) o = (⟨none, initσ c.tm, mkStk (fun _ => []) [] [] [] [] o⟩ : ICfg c.tm) := by
  unfold haltList
  congr 1
  funext k
  cases k <;> rfl

theorem initList_orig (M : FinTM2) (s : List (M.Γ M.k₀)) :
    initList M s = (⟨some M.main, M.initialState, Function.update (fun _ => []) M.k₀ s⟩ :
      TM2.Cfg M.Γ M.Λ M.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = M.k₀
  · subst h; simp
  · simp [h]

theorem haltList_orig (M : FinTM2) (s : List (M.Γ M.k₁)) :
    haltList M s = (⟨none, M.initialState, Function.update (fun _ => []) M.k₁ s⟩ :
      TM2.Cfg M.Γ M.Λ M.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = M.k₁
  · subst h; simp
  · simp [h]

def embCfg {M : FinTM2} (acc curB : Bool) (lu rv : List Bool) (cfg : TM2.Cfg M.Γ M.Λ M.σ) : ICfg M :=
  ⟨some (cfg.l.elim .afterM .orig), (cfg.var, acc, curB, none), mkStk cfg.stk lu rv [] [] []⟩

theorem simM_aux {M : FinTM2} (acc curB : Bool) (lu rv : List Bool)
    (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trM q) ((v, acc, curB, none) : Iσ M) (mkStk S lu rv [] [] []) =
      embCfg acc curB lu rv (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k fn q ih =>
    have := ih v (Function.update S k (fn v :: S k))
    rw [← upd_orig] at this
    exact this
  | peek k fn q ih => exact ih _ _
  | pop k fn q ih =>
    have := ih (fn v (S k).head?) (Function.update S k (S k).tail)
    rw [← upd_orig] at this
    exact this
  | load fn q ih => exact ih _ _
  | branch fn q₁ q₂ ih₁ ih₂ =>
    simp only [trM, TM2.stepAux]
    cases fn v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto fn => rfl
  | halt => rfl

theorem step_simM {f : List Bool → Bool}
    (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f)
    (acc curB : Bool) (lu rv : List Bool) (cfg cfg' : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ)
    (h : TM2.step c.tm.m cfg = some cfg') :
    TM2.step (iProg c) (embCfg acc curB lu rv cfg) = some (embCfg acc curB lu rv cfg') := by
  obtain ⟨l, v, S⟩ := cfg
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simM_aux acc curB lu rv (c.tm.m l) v S)

section steps

variable {f : List Bool → Bool}
variable (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f)

theorem step_next_nil (acc : Bool) (lu : List Bool) :
    TM2.step (iProg c)
        (⟨some .next, (c.tm.initialState, acc, false, none), mkStk (fun _ => []) lu [] [] [] []⟩ : ICfg c.tm) =
      some ⟨some .drainLU, (c.tm.initialState, acc, false, none), mkStk (fun _ => []) lu [] [] [] []⟩ := by
  simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  rw [upd_rv]

theorem step_next_cons (acc b : Bool) (lu v : List Bool) :
    TM2.step (iProg c)
        (⟨some .next, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) lu (b :: v) [] [] []⟩ : ICfg c.tm) =
      some ⟨some .revV, (c.tm.initialState, acc, b, none),
        mkStk (fun _ => []) lu v [] [] []⟩ := by
  simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [upd_rv]

theorem loop_revV (acc curB : Bool) (lu rv tv : List Bool) :
    (flip bind (TM2.step (iProg c)))^[rv.length + 1]
        (some (⟨some .revV, (c.tm.initialState, acc, curB, none),
          mkStk (fun _ => []) lu rv [] tv []⟩ : ICfg c.tm)) =
      some ⟨some .loadV, (c.tm.initialState, acc, curB, none),
        mkStk (fun _ => []) lu [] [] (rv.reverse ++ tv) []⟩ := by
  induction rv generalizing tv with
  | nil =>
    have hst : TM2.step (iProg c)
        (⟨some .revV, (c.tm.initialState, acc, curB, none),
          mkStk (fun _ => []) lu [] [] tv []⟩ : ICfg c.tm) =
        some ⟨some .loadV, (c.tm.initialState, acc, curB, none),
          mkStk (fun _ => []) lu [] [] tv []⟩ := by
      simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_rv]
    exact hst
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (iProg c)
        (⟨some .revV, (c.tm.initialState, acc, curB, none),
          mkStk (fun _ => []) lu (a :: xs) [] tv []⟩ : ICfg c.tm) =
        some ⟨some .revV, (c.tm.initialState, acc, curB, none),
          mkStk (fun _ => []) lu xs [] (a :: tv) []⟩ := by
      simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_rv, upd_tv]
      rfl
    have e : flip bind (TM2.step (iProg c))
        (some (⟨some .revV, (c.tm.initialState, acc, curB, none),
          mkStk (fun _ => []) lu (a :: xs) [] tv []⟩ : ICfg c.tm)) =
        some ⟨some .revV, (c.tm.initialState, acc, curB, none),
          mkStk (fun _ => []) lu xs [] (a :: tv) []⟩ := hst
    rw [e, ih (a :: tv)]
    simp

theorem loop_loadV (acc curB : Bool) (lu rv tv : List Bool) (s0 : List (c.tm.Γ c.tm.k₀)) :
    (flip bind (TM2.step (iProg c)))^[tv.length + 1]
        (some (⟨some .loadV, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) lu rv [] tv []⟩ : ICfg c.tm)) =
      some ⟨some .loadU, (c.tm.initialState, acc, curB, none),
        mkStk (Function.update (fun _ => []) c.tm.k₀ (tv.reverse.map c.inputAlphabet.invFun ++ s0))
          lu (tv.reverse ++ rv) [] [] []⟩ := by
  induction tv generalizing rv s0 with
  | nil =>
    have hst : TM2.step (iProg c)
        (⟨some .loadV, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) lu rv [] [] []⟩ : ICfg c.tm) =
        some ⟨some .loadU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) lu rv [] [] []⟩ := by
      simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_tv]
    exact hst
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (iProg c)
        (⟨some .loadV, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) lu rv [] (a :: xs) []⟩ : ICfg c.tm) =
        some ⟨some .loadV, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ (c.inputAlphabet.invFun a :: s0))
            lu (a :: rv) [] xs []⟩ := by
      simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_tv, upd_rv, upd_orig]
      simp only [mkStk, Function.update_self, Function.update_idem]
    have e : flip bind (TM2.step (iProg c))
        (some (⟨some .loadV, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) lu rv [] (a :: xs) []⟩ : ICfg c.tm)) =
        some ⟨some .loadV, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ (c.inputAlphabet.invFun a :: s0))
            lu (a :: rv) [] xs []⟩ := hst
    rw [e, ih (a :: rv) (c.inputAlphabet.invFun a :: s0)]
    simp

theorem loop_loadU (acc curB : Bool) (lu rv tu : List Bool) (s0 : List (c.tm.Γ c.tm.k₀)) :
    (flip bind (TM2.step (iProg c)))^[lu.length + 1]
        (some (⟨some .loadU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) lu rv tu [] []⟩ : ICfg c.tm)) =
      some ⟨some .restoreU, (c.tm.initialState, acc, curB, none),
        mkStk (Function.update (fun _ => []) c.tm.k₀ (lu.reverse.map c.inputAlphabet.invFun ++ s0))
          [] rv (lu.reverse ++ tu) [] []⟩ := by
  induction lu generalizing tu s0 with
  | nil =>
    have hst : TM2.step (iProg c)
        (⟨some .loadU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rv tu [] []⟩ : ICfg c.tm) =
        some ⟨some .restoreU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rv tu [] []⟩ := by
      simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_lu]
    exact hst
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (iProg c)
        (⟨some .loadU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) (a :: xs) rv tu [] []⟩ : ICfg c.tm) =
        some ⟨some .loadU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ (c.inputAlphabet.invFun a :: s0))
            xs rv (a :: tu) [] []⟩ := by
      simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_lu, upd_tu, upd_orig]
      simp only [mkStk, Function.update_self, Function.update_idem]
    have e : flip bind (TM2.step (iProg c))
        (some (⟨some .loadU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) (a :: xs) rv tu [] []⟩ : ICfg c.tm)) =
        some ⟨some .loadU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ (c.inputAlphabet.invFun a :: s0))
            xs rv (a :: tu) [] []⟩ := hst
    rw [e, ih (a :: tu) (c.inputAlphabet.invFun a :: s0)]
    simp

theorem loop_restoreU (acc curB : Bool) (lu rv tu : List Bool) (s0 : List (c.tm.Γ c.tm.k₀)) :
    (flip bind (TM2.step (iProg c)))^[tu.length + 1]
        (some (⟨some .restoreU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) lu rv tu [] []⟩ : ICfg c.tm)) =
      some ⟨some (.orig c.tm.main), (c.tm.initialState, acc, curB, none),
        mkStk (Function.update (fun _ => []) c.tm.k₀ s0) (tu.reverse ++ lu) rv [] [] []⟩ := by
  induction tu generalizing lu with
  | nil =>
    have hst : TM2.step (iProg c)
        (⟨some .restoreU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) lu rv [] [] []⟩ : ICfg c.tm) =
        some ⟨some (.orig c.tm.main), (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) lu rv [] [] []⟩ := by
      simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_tu]
    exact hst
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (iProg c)
        (⟨some .restoreU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) lu rv (a :: xs) [] []⟩ : ICfg c.tm) =
        some ⟨some .restoreU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) (a :: lu) rv xs [] []⟩ := by
      simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_tu, upd_lu]
      rfl
    have e : flip bind (TM2.step (iProg c))
        (some (⟨some .restoreU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) lu rv (a :: xs) [] []⟩ : ICfg c.tm)) =
        some ⟨some .restoreU, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) (a :: lu) rv xs [] []⟩ := hst
    rw [e, ih (a :: lu)]
    simp

theorem step_afterM (acc curB b : Bool) (lu rv : List Bool) :
    TM2.step (iProg c)
        (⟨some .afterM, (c.tm.initialState, acc, curB, none),
          mkStk (Function.update (fun _ => []) c.tm.k₁ [c.outputAlphabet.invFun b])
            lu rv [] [] []⟩ : ICfg c.tm) =
      some ⟨some .next, (c.tm.initialState, acc || b, false, none),
        mkStk (fun _ => []) (curB :: lu) rv [] [] []⟩ := by
  simp only [TM2.step, iProg, TM2.stepAux, mkStk, Function.update_self, List.head?_cons,
    List.tail_cons, Option.map_some]
  rw [upd_orig]
  have hclr : Function.update (Function.update (fun _ : c.tm.K => []) c.tm.k₁ [c.outputAlphabet.invFun b])
      c.tm.k₁ [] = fun _ => [] := by
    rw [Function.update_idem, Function.update_eq_self_iff]
  rw [hclr, upd_lu]
  simp [mkStk]

theorem loop_drainLU (acc : Bool) (lu : List Bool) :
    (flip bind (TM2.step (iProg c)))^[lu.length + 1]
        (some (⟨some .drainLU, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) lu [] [] [] []⟩ : ICfg c.tm)) =
      some ⟨none, initσ c.tm, mkStk (fun _ => []) [] [] [] [] [acc]⟩ := by
  induction lu with
  | nil =>
    have hst : TM2.step (iProg c)
        (⟨some .drainLU, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] [] [] [] []⟩ : ICfg c.tm) =
        some ⟨none, initσ c.tm, mkStk (fun _ => []) [] [] [] [] [acc]⟩ := by
      simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_lu, upd_out]
      rfl
    exact hst
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (iProg c)
        (⟨some .drainLU, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) (a :: xs) [] [] [] []⟩ : ICfg c.tm) =
        some ⟨some .drainLU, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) xs [] [] [] []⟩ := by
      simp only [TM2.step, iProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true]
      rw [upd_lu]
    have e : flip bind (TM2.step (iProg c))
        (some (⟨some .drainLU, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) (a :: xs) [] [] [] []⟩ : ICfg c.tm)) =
        some ⟨some .drainLU, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) xs [] [] [] []⟩ := hst
    rw [e, ih]

theorem run_one_zip (lu v : List Bool) (b acc : Bool) :
    ∃ t : ℕ, t ≤ 2 * (lu.length + v.length) + 6 + c.time (lu.length + v.length) ∧
      (flip bind (TM2.step (iProg c)))^[t]
          (some (⟨some .next, (c.tm.initialState, acc, false, none),
            mkStk (fun _ => []) lu (b :: v) [] [] []⟩ : ICfg c.tm)) =
        some ⟨some .next, (c.tm.initialState, acc || f (lu.reverse ++ v), false, none),
          mkStk (fun _ => []) (b :: lu) v [] [] []⟩ := by
  let z : List Bool := lu.reverse ++ v
  have hzlen : z.length = lu.length + v.length := by
    simp [z]
  let outM := c.outputsFun z
  have hsteps_le : outM.steps ≤ c.time (lu.length + v.length) := by
    have henc : (PvsNP.encodeString z).length = lu.length + v.length := by
      simpa [PvsNP.encodeString, Computability.encodingList] using hzlen
    exact outM.steps_le_m.trans (le_of_eq (congrArg c.time henc))
  have hrunM :
      (flip bind (TM2.step (iProg c)))^[outM.steps]
          (some (⟨some (.orig c.tm.main), (c.tm.initialState, acc, b, none),
            mkStk (Function.update (fun _ => []) c.tm.k₀ (z.map c.inputAlphabet.invFun))
              lu v [] [] []⟩ : ICfg c.tm)) =
        some ⟨some .afterM, (c.tm.initialState, acc, b, none),
          mkStk (Function.update (fun _ => []) c.tm.k₁ [c.outputAlphabet.invFun (f z)])
            lu v [] [] []⟩ := by
    have hev : (flip bind (TM2.step c.tm.m))^[outM.steps]
        (some (initList c.tm (z.map c.inputAlphabet.invFun))) =
        some (haltList c.tm [c.outputAlphabet.invFun (f z)]) := outM.evals_in_steps
    have hsim := simulate_run (TM2.step c.tm.m) (TM2.step (iProg c))
      (embCfg acc b lu v) (step_simM c acc b lu v) outM.steps
      (initList c.tm (z.map c.inputAlphabet.invFun))
      (haltList c.tm [c.outputAlphabet.invFun (f z)]) hev
    have hinitE : embCfg acc b lu v (initList c.tm (z.map c.inputAlphabet.invFun)) =
        ⟨some (.orig c.tm.main), (c.tm.initialState, acc, b, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ (z.map c.inputAlphabet.invFun))
            lu v [] [] []⟩ := by
      rw [initList_orig]; rfl
    have hhaltE : embCfg acc b lu v (haltList c.tm [c.outputAlphabet.invFun (f z)]) =
        ⟨some .afterM, (c.tm.initialState, acc, b, none),
          mkStk (Function.update (fun _ => []) c.tm.k₁ [c.outputAlphabet.invFun (f z)])
            lu v [] [] []⟩ := by
      rw [haltList_orig]; rfl
    rw [hinitE, hhaltE] at hsim
    exact hsim
  let t : ℕ := 1 + outM.steps + (lu.length + 1) + (lu.length + 1) + (v.length + 1) + (v.length + 1) + 1
  refine ⟨t, by dsimp only [t]; omega, ?_⟩
  dsimp only [t]
  have hupd0 : Function.update (fun k : c.tm.K => ([] : List (c.tm.Γ k))) c.tm.k₀ [] =
      (fun k : c.tm.K => ([] : List (c.tm.Γ k))) := by
    funext k
    by_cases h : k = c.tm.k₀
    · subst h; simp
    · simp [h]
  rw [Function.iterate_add_apply]
  have hnxt : (flip bind (TM2.step (iProg c)))^[1]
      (some (⟨some .next, (c.tm.initialState, acc, false, none),
        mkStk (fun _ => []) lu (b :: v) [] [] []⟩ : ICfg c.tm)) =
      some ⟨some .revV, (c.tm.initialState, acc, b, none),
        mkStk (fun _ => []) lu v [] [] []⟩ :=
    step_next_cons c acc b lu v
  rw [hnxt, Function.iterate_add_apply]
  have hrv := loop_revV c acc b lu v []
  rw [List.append_nil] at hrv
  rw [hrv, Function.iterate_add_apply]
  have hlv := loop_loadV c acc b lu [] v.reverse []
  rw [List.length_reverse, List.reverse_reverse, List.append_nil, List.append_nil] at hlv
  rw [hupd0] at hlv
  rw [hlv, Function.iterate_add_apply]
  have hlu := loop_loadU c acc b lu v [] (v.map c.inputAlphabet.invFun)
  rw [List.append_nil] at hlu
  rw [hlu, Function.iterate_add_apply]
  have hru := loop_restoreU c acc b [] v lu.reverse
    (lu.reverse.map c.inputAlphabet.invFun ++ v.map c.inputAlphabet.invFun)
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at hru
  rw [hru, Function.iterate_add_apply]
  have hzmap : lu.reverse.map c.inputAlphabet.invFun ++ v.map c.inputAlphabet.invFun =
      z.map c.inputAlphabet.invFun := by
    simp [z]
  rw [hzmap, hrunM]
  exact step_afterM c acc b (f z) lu v

theorem loop_zip (k : ℕ) (htime : ∀ m : ℕ, c.time m ≤ 2 ^ (m ^ k) + k) (n : ℕ) :
    ∀ (rv lu : List Bool) (acc : Bool),
      lu.length + rv.length = n →
      ∃ (t : ℕ) (res : Bool),
        t ≤ rv.length * (2 * n + 6 + (2 ^ (n ^ k) + k)) + (n + 2) ∧
        (res = true ↔ acc = true ∨
          ∃ (u1 v1 : List Bool) (b : Bool), rv = u1 ++ b :: v1 ∧
            f (lu.reverse ++ u1 ++ v1) = true) ∧
        (flip bind (TM2.step (iProg c)))^[t]
            (some (⟨some .next, (c.tm.initialState, acc, false, none),
              mkStk (fun _ => []) lu rv [] [] []⟩ : ICfg c.tm)) =
          some ⟨none, initσ c.tm, mkStk (fun _ => []) [] [] [] [] [res]⟩ := by
  intro rv
  induction rv with
  | nil =>
    intro lu acc hlen
    have hlulen : lu.length = n := by simpa using hlen
    refine ⟨(lu.length + 1) + 1, acc, by omega, ?_, ?_⟩
    · constructor
      · intro ha; exact Or.inl ha
      · rintro (ha | ⟨u1, v1, b, hnil, _⟩)
        · exact ha
        · cases u1 <;> simp at hnil
    · rw [Function.iterate_add_apply]
      have hnxt : (flip bind (TM2.step (iProg c)))^[1]
          (some (⟨some .next, (c.tm.initialState, acc, false, none),
            mkStk (fun _ => []) lu [] [] [] []⟩ : ICfg c.tm)) =
          some ⟨some .drainLU, (c.tm.initialState, acc, false, none),
            mkStk (fun _ => []) lu [] [] [] []⟩ :=
        step_next_nil c acc lu
      rw [hnxt]
      exact loop_drainLU c acc lu
  | cons b v ih =>
    intro lu acc hlen
    obtain ⟨t1, ht1, hrun1⟩ := run_one_zip c lu v b acc
    have hct : c.time (lu.length + v.length) ≤ 2 ^ (n ^ k) + k := by
      have h1 := htime (lu.length + v.length)
      have hle : lu.length + v.length ≤ n := by simp only [List.length_cons] at hlen; omega
      have hpow : (lu.length + v.length) ^ k ≤ n ^ k := Nat.pow_le_pow_left hle k
      have h2pow : 2 ^ ((lu.length + v.length) ^ k) ≤ 2 ^ (n ^ k) := Nat.pow_le_pow_right (by omega) hpow
      omega
    obtain ⟨t2, res, ht2, hresIff, hrun2⟩ :=
      ih (b :: lu) (acc || f (lu.reverse ++ v)) (by simp only [List.length_cons] at hlen ⊢; omega)
    refine ⟨t2 + t1, res, ?_, ?_, ?_⟩
    · have hmul : (v.length + 1) * (2 * n + 6 + (2 ^ (n ^ k) + k)) =
          v.length * (2 * n + 6 + (2 ^ (n ^ k) + k)) + (2 * n + 6 + (2 ^ (n ^ k) + k)) := by ring
      simp only [List.length_cons] at hlen ⊢
      omega
    · rw [hresIff]
      constructor
      · rintro (hacc1 | ⟨u1, v1, b', hv, hfv⟩)
        · rcases Bool.or_eq_true_iff.mp hacc1 with ha | hfz
          · exact Or.inl ha
          · right
            exact ⟨[], v, b, rfl, by simpa using hfz⟩
        · right
          refine ⟨b :: u1, v1, b', by simp [hv], ?_⟩
          simpa [List.reverse_cons, List.append_assoc] using hfv
      · rintro (ha | ⟨u1, v1, b', hbv, hfv⟩)
        · left; simp [ha]
        · cases u1 with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hbv
            rcases hbv with ⟨rfl, rfl⟩
            left
            simp only [List.append_nil] at hfv
            simp [hfv]
          | cons a u1' =>
            simp only [List.cons_append, List.cons.injEq] at hbv
            rcases hbv with ⟨rfl, rfl⟩
            right
            refine ⟨u1', v1, b', rfl, ?_⟩
            simpa [List.reverse_cons, List.append_assoc] using hfv
    · rw [Function.iterate_add_apply, hrun1]
      exact hrun2

end steps

theorem tc_exp_ins_one_aux (L : Language Bool) :
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, (∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ v ∈ L) ↔ f x = true) ∧
          ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  classical
  rintro ⟨k, f, c, hdec, htime⟩
  let fI : List Bool → Bool :=
    fun x => decide (∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ v ∈ L)
  have hfI : ∀ x : List Bool,
      (∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ v ∈ L) ↔ fI x = true := by
    intro x
    simp [fI]
  obtain ⟨p, hp⟩ := ins_time_le_exp_poly k
  obtain ⟨K, hK⟩ := exp_poly_bound p
  have hrun : ∀ x : List Bool,
      ∃ t : ℕ, t ≤ 2 ^ (x.length ^ K) + K ∧
        (flip bind (TM2.step (iProg c)))^[t] (some (initList (insTM c) x)) =
          some (haltList (insTM c) [fI x]) := by
    intro x
    obtain ⟨t, res, ht, hresIff, hzip⟩ := loop_zip c k htime x.length x [] false (by simp)
    have hres_eq : res = fI x := by
      apply Bool.eq_iff_iff.mpr
      rw [hresIff, ← hfI x]
      constructor
      · rintro (hfalse | ⟨u, v, b, hx, hfu⟩)
        · exact absurd hfalse (by decide)
        · simp only [List.reverse_nil, List.nil_append] at hfu
          exact ⟨u, v, b, hx, (hdec (u ++ v)).mpr hfu⟩
      · rintro ⟨u, v, b, hx, huL⟩
        right
        exact ⟨u, v, b, hx, by simpa using (hdec (u ++ v)).mp huL⟩
    have ht_le : t ≤ 2 ^ (x.length ^ K) + K :=
      ht.trans ((hp x.length).trans (hK x.length))
    refine ⟨t, ht_le, ?_⟩
    refine (congrArg (fun cfg => (flip bind (TM2.step (iProg c)))^[t] (some cfg))
      (initList_insTM c x)).trans
      (Eq.trans ?_ (congrArg some (haltList_insTM c [fI x])).symm)
    rw [← hres_eq]
    exact hzip
  let M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer fI :=
    { tm := insTM c
      inputAlphabet := Equiv.refl _
      outputAlphabet := Equiv.refl _
      time := fun n => 2 ^ (n ^ K) + K
      outputsFun := fun x =>
        let h := hrun x
        { steps := Classical.choose h
          evals_in_steps := by
            have hspec := Classical.choose_spec h
            have hm1 : List.map (Equiv.refl Bool).invFun (PvsNP.encodeString x) = x := by
              simp [PvsNP.encodeString, Computability.encodingList]
            have hm2 : List.map (Equiv.refl Bool).invFun (PvsNP.encodeAnswer (fI x)) = [fI x] := by
              simp [PvsNP.encodeAnswer, Computability.encodeBool]
            exact (congrArg (fun i => (flip bind (TM2.step (iProg c)))^[Classical.choose h]
              (some (initList (insTM c) i))) hm1).trans
              (hspec.2.trans (congrArg (fun o => some (haltList (insTM c) o)) hm2.symm))
          steps_le_m := by
            have hspec := Classical.choose_spec h
            have hlen : (PvsNP.encodeString x).length = x.length := by
              simp [PvsNP.encodeString, Computability.encodingList]
            rw [hlen]
            exact hspec.1 } }
  exact ⟨K, fI, M, hfI, fun _ => le_refl _⟩

end PvsNP.Units.tc_exp_ins_one

/-- Exponential time is closed under inserting one bit (TM2). -/
theorem PvsNP.Units.tc_exp_ins_one :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ (u v : List Bool) (b : Bool), x = u ++ b :: v ∧ u ++ v ∈ L) ↔ f x = true) ∧
            ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_ins_one.tc_exp_ins_one_aux
