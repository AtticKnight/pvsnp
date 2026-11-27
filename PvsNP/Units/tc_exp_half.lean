import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.tc_exp_half

open Turing

theorem two_pow_add_le (a b : ℕ) : 2 ^ a + b ≤ 2 ^ (a + b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hpos : 1 ≤ 2 ^ (a + b) := Nat.one_le_two_pow
    have hpow : 2 ^ (a + (b + 1)) = 2 ^ (a + b) * 2 := by
      rw [← Nat.add_assoc, Nat.pow_succ]
    rw [hpow]
    omega

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

theorem half_time_le_exp_poly (k : ℕ) :
    ∃ p : Polynomial ℕ, ∀ n : ℕ,
      (n + 1) + 2 ^ n * (6 * n + 7 + (2 ^ ((2 * n) ^ k) + k)) + (2 * n + 2) ≤ 2 ^ p.eval n := by
  let p : Polynomial ℕ :=
    Polynomial.C (2 ^ k) * Polynomial.X ^ k + Polynomial.C 10 * Polynomial.X + Polynomial.C (11 + k)
  refine ⟨p, fun n => ?_⟩
  have h1 : 9 * n + 10 + k ≤ 2 ^ (9 * n + 10 + k) := Nat.le_of_lt Nat.lt_two_pow_self
  have h2 : 2 ^ (9 * n + 10 + k) ≤ 2 ^ (9 * n + 10 + k + (2 * n) ^ k) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_add_right _ _)
  have h3 : 2 ^ ((2 * n) ^ k) ≤ 2 ^ (9 * n + 10 + k + (2 * n) ^ k) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_add_left _ _)
  have h4 : 9 * n + 10 + k + 2 ^ ((2 * n) ^ k) ≤ 2 ^ (9 * n + 10 + k + (2 * n) ^ k + 1) := by
    rw [Nat.pow_succ]
    have h12 := h1.trans h2
    omega
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have htot : (n + 1) + 2 ^ n * (6 * n + 7 + (2 ^ ((2 * n) ^ k) + k)) + (2 * n + 2) ≤
      2 ^ n * (9 * n + 10 + k + 2 ^ ((2 * n) ^ k)) := by
    have hlin : (n + 1) + (2 * n + 2) ≤ 2 ^ n * (3 * n + 3) := by
      calc (n + 1) + (2 * n + 2) = 1 * (3 * n + 3) := by ring
        _ ≤ 2 ^ n * (3 * n + 3) := Nat.mul_le_mul_right _ h2n
    calc (n + 1) + 2 ^ n * (6 * n + 7 + (2 ^ ((2 * n) ^ k) + k)) + (2 * n + 2)
        = 2 ^ n * (6 * n + 7 + 2 ^ ((2 * n) ^ k) + k) + ((n + 1) + (2 * n + 2)) := by ring
      _ ≤ 2 ^ n * (6 * n + 7 + 2 ^ ((2 * n) ^ k) + k) + 2 ^ n * (3 * n + 3) :=
          Nat.add_le_add_left hlin _
      _ = 2 ^ n * (9 * n + 10 + k + 2 ^ ((2 * n) ^ k)) := by ring
  have hmul : 2 ^ n * (9 * n + 10 + k + 2 ^ ((2 * n) ^ k)) ≤
      2 ^ (n + (9 * n + 10 + k + (2 * n) ^ k + 1)) := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_left _ h4
  have hpeval : p.eval n = n + (9 * n + 10 + k + (2 * n) ^ k + 1) := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Nat.mul_pow]
    ring
  rw [hpeval]
  exact htot.trans hmul

def incStep (carry : Bool) : List Bool → Bool × List Bool
  | [] => (carry, [])
  | b :: rest =>
    let r := incStep (carry && b) rest
    (r.1, xor carry b :: r.2)

theorem incStep_len (carry : Bool) (c : List Bool) :
    (incStep carry c).2.length = c.length := by
  induction c generalizing carry with
  | nil => rfl
  | cons b rest ih =>
    simp only [incStep, List.length_cons, ih]

theorem incStep_val (carry : Bool) (c : List Bool) :
    Nat.ofDigits (2 : ℕ) ((incStep carry c).2.map Bool.toNat) +
        (incStep carry c).1.toNat * 2 ^ c.length =
      Nat.ofDigits (2 : ℕ) (c.map Bool.toNat) + carry.toNat := by
  induction c generalizing carry with
  | nil => simp [incStep]
  | cons b rest ih =>
    simp only [incStep, List.map_cons, Nat.ofDigits_cons, List.length_cons, Nat.pow_succ]
    have h := ih (carry && b)
    have hbit : (xor carry b).toNat + 2 * (carry && b).toNat = b.toNat + carry.toNat := by
      cases carry <;> cases b <;> rfl
    calc (xor carry b).toNat + 2 * Nat.ofDigits (2 : ℕ) ((incStep (carry && b) rest).2.map Bool.toNat) +
          (incStep (carry && b) rest).1.toNat * (2 ^ rest.length * 2)
        = (xor carry b).toNat +
            2 * (Nat.ofDigits (2 : ℕ) ((incStep (carry && b) rest).2.map Bool.toNat) +
              (incStep (carry && b) rest).1.toNat * 2 ^ rest.length) := by ring
      _ = (xor carry b).toNat +
            2 * (Nat.ofDigits (2 : ℕ) (rest.map Bool.toNat) + (carry && b).toNat) := by rw [h]
      _ = ((xor carry b).toNat + 2 * (carry && b).toNat) +
            2 * Nat.ofDigits (2 : ℕ) (rest.map Bool.toNat) := by ring
      _ = (b.toNat + carry.toNat) + 2 * Nat.ofDigits (2 : ℕ) (rest.map Bool.toNat) := by rw [hbit]
      _ = b.toNat + 2 * Nat.ofDigits (2 : ℕ) (rest.map Bool.toNat) + carry.toNat := by ring

theorem ofDigits_bool_lt (c : List Bool) :
    Nat.ofDigits (2 : ℕ) (c.map Bool.toNat) < 2 ^ c.length := by
  induction c with
  | nil => simp
  | cons b rest ih =>
    simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem ofDigits_bool_inj : ∀ {u v : List Bool}, u.length = v.length →
    Nat.ofDigits (2 : ℕ) (u.map Bool.toNat) = Nat.ofDigits (2 : ℕ) (v.map Bool.toNat) → u = v
  | [], [], _, _ => rfl
  | a :: u, b :: v, hlen, hval => by
    simp only [List.map_cons, Nat.ofDigits_cons] at hval
    have hab : a = b := by
      cases a <;> cases b <;> simp at hval ⊢ <;> omega
    subst hab
    have huv : Nat.ofDigits (2 : ℕ) (u.map Bool.toNat) = Nat.ofDigits (2 : ℕ) (v.map Bool.toNat) := by
      omega
    exact congrArg (a :: ·) (ofDigits_bool_inj (by simpa using hlen) huv)

theorem ofDigits_replicate_false (n : ℕ) :
    Nat.ofDigits (2 : ℕ) ((List.replicate n false).map Bool.toNat) = 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.map_cons, Nat.ofDigits_cons, ih]
    simp

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

inductive WStk (K : Type)
  | orig (k : K) | inp | rx | sx | cy | ty | out
  deriving DecidableEq

def wStkEquiv (K : Type) : WStk K ≃ K ⊕ Fin 6 where
  toFun
    | .orig k => Sum.inl k
    | .inp => Sum.inr 0
    | .rx => Sum.inr 1
    | .sx => Sum.inr 2
    | .cy => Sum.inr 3
    | .ty => Sum.inr 4
    | .out => Sum.inr 5
  invFun
    | Sum.inl k => .orig k
    | Sum.inr ⟨0, _⟩ => .inp
    | Sum.inr ⟨1, _⟩ => .rx
    | Sum.inr ⟨2, _⟩ => .sx
    | Sum.inr ⟨3, _⟩ => .cy
    | Sum.inr ⟨4, _⟩ => .ty
    | Sum.inr ⟨5, _⟩ => .out
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with k | i
    · rfl
    · fin_cases i <;> rfl

instance instFintypeWStk (K : Type) [Fintype K] : Fintype (WStk K) :=
  Fintype.ofEquiv (K ⊕ Fin 6) (wStkEquiv K).symm

inductive WLbl (Λ : Type)
  | orig (l : Λ)
  | init | loadY | restoreY | loadX | restoreX | afterM | inc | unrevInc | drainTY | drainRX
  deriving DecidableEq

def wLblEquiv (Λ : Type) : WLbl Λ ≃ Λ ⊕ Fin 10 where
  toFun
    | .orig l => Sum.inl l
    | .init => Sum.inr 0
    | .loadY => Sum.inr 1
    | .restoreY => Sum.inr 2
    | .loadX => Sum.inr 3
    | .restoreX => Sum.inr 4
    | .afterM => Sum.inr 5
    | .inc => Sum.inr 6
    | .unrevInc => Sum.inr 7
    | .drainTY => Sum.inr 8
    | .drainRX => Sum.inr 9
  invFun
    | Sum.inl l => .orig l
    | Sum.inr ⟨0, _⟩ => .init
    | Sum.inr ⟨1, _⟩ => .loadY
    | Sum.inr ⟨2, _⟩ => .restoreY
    | Sum.inr ⟨3, _⟩ => .loadX
    | Sum.inr ⟨4, _⟩ => .restoreX
    | Sum.inr ⟨5, _⟩ => .afterM
    | Sum.inr ⟨6, _⟩ => .inc
    | Sum.inr ⟨7, _⟩ => .unrevInc
    | Sum.inr ⟨8, _⟩ => .drainTY
    | Sum.inr ⟨9, _⟩ => .drainRX
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with l | i
    · rfl
    · fin_cases i <;> rfl

instance instFintypeWLbl (Λ : Type) [Fintype Λ] : Fintype (WLbl Λ) :=
  Fintype.ofEquiv (Λ ⊕ Fin 10) (wLblEquiv Λ).symm

abbrev WΓ (M : FinTM2) : WStk M.K → Type
  | .orig k => M.Γ k
  | _ => Bool

abbrev Wσ (M : FinTM2) : Type := M.σ × Bool × Bool × Option Bool

def initσ (M : FinTM2) : Wσ M := (M.initialState, false, false, none)

def trM {M : FinTM2} : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (WΓ M) (WLbl M.Λ) (Wσ M)
  | .push k f q => .push (.orig k) (fun st => f st.1) (trM q)
  | .peek k f q => .peek (.orig k) (fun st o => (f st.1 o, st.2)) (trM q)
  | .pop k f q => .pop (.orig k) (fun st o => (f st.1 o, st.2)) (trM q)
  | .load a q => .load (fun st => (a st.1, st.2)) (trM q)
  | .branch f q₁ q₂ => .branch (fun st => f st.1) (trM q₁) (trM q₂)
  | .goto f => .goto (fun st => .orig (f st.1))
  | .halt => .goto (fun _ => .afterM)

def wProg {f : List Bool → Bool}
    (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) :
    WLbl c.tm.Λ → TM2.Stmt (WΓ c.tm) (WLbl c.tm.Λ) (Wσ c.tm)
  | .orig l => trM (c.tm.m l)
  | .init =>
    .pop .inp (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.push .rx (fun st => st.2.2.2.getD false)
          (.push .cy (fun _ => false)
            (.load (fun _ => initσ c.tm) (.goto fun _ => .init))))
        (.load (fun _ => initσ c.tm) (.goto fun _ => .loadY)))
  | .loadY =>
    .pop .cy (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.push .ty (fun st => st.2.2.2.getD false)
          (.push (.orig c.tm.k₀) (fun st => c.inputAlphabet.invFun (st.2.2.2.getD false))
            (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .loadY))))
        (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .restoreY)))
  | .restoreY =>
    .pop .ty (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.push .cy (fun st => st.2.2.2.getD false)
          (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .restoreY)))
        (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .loadX)))
  | .loadX =>
    .pop .rx (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.push .sx (fun st => st.2.2.2.getD false)
          (.push (.orig c.tm.k₀) (fun st => c.inputAlphabet.invFun (st.2.2.2.getD false))
            (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .loadX))))
        (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .restoreX)))
  | .restoreX =>
    .pop .sx (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.push .rx (fun st => st.2.2.2.getD false)
          (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .restoreX)))
        (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .orig c.tm.main)))
  | .afterM =>
    .pop (.orig c.tm.k₁)
      (fun st o =>
        (c.tm.initialState, st.2.1 || (o.map c.outputAlphabet == some true), true, none))
      (.goto fun _ => .inc)
  | .inc =>
    .pop .cy (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.push .ty (fun st => xor st.2.2.1 (st.2.2.2.getD false))
          (.load (fun st => (c.tm.initialState, st.2.1, st.2.2.1 && st.2.2.2.getD false, none))
            (.goto fun _ => .inc)))
        (.branch (fun st => st.2.2.1)
          (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .drainTY))
          (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .unrevInc))))
  | .unrevInc =>
    .pop .ty (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.push .cy (fun st => st.2.2.2.getD false)
          (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .unrevInc)))
        (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .loadY)))
  | .drainTY =>
    .pop .ty (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .drainTY))
        (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .drainRX)))
  | .drainRX =>
    .pop .rx (fun st o => (st.1, st.2.1, st.2.2.1, o))
      (.branch (fun st => st.2.2.2.isSome)
        (.load (fun st => (c.tm.initialState, st.2.1, false, none)) (.goto fun _ => .drainRX))
        (.push .out (fun st => st.2.1)
          (.load (fun _ => initσ c.tm) .halt)))

def halfTM {f : List Bool → Bool}
    (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) : FinTM2 :=
  haveI := c.tm.kFin
  haveI := c.tm.ΛFin
  haveI := c.tm.σFin
  { K := WStk c.tm.K
    k₀ := .inp
    k₁ := .out
    Γ := WΓ c.tm
    Λ := WLbl c.tm.Λ
    main := .init
    σ := Wσ c.tm
    initialState := initσ c.tm
    m := wProg c }

abbrev WCfg (M : FinTM2) : Type := TM2.Cfg (WΓ M) (WLbl M.Λ) (Wσ M)

def mkStk {M : FinTM2} (S : ∀ k, List (M.Γ k))
    (i rx sx cy ty o : List Bool) : ∀ k, List (WΓ M k)
  | .orig k => S k
  | .inp => i
  | .rx => rx
  | .sx => sx
  | .cy => cy
  | .ty => ty
  | .out => o

theorem upd_orig {M : FinTM2} (S : ∀ k, List (M.Γ k)) (k : M.K) (v : List (M.Γ k))
    (i rx sx cy ty o : List Bool) :
    Function.update (mkStk S i rx sx cy ty o) (.orig k) v =
      mkStk (Function.update S k v) i rx sx cy ty o := by
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
  | inp => rw [Function.update_of_ne (by simp)]; rfl
  | rx => rw [Function.update_of_ne (by simp)]; rfl
  | sx => rw [Function.update_of_ne (by simp)]; rfl
  | cy => rw [Function.update_of_ne (by simp)]; rfl
  | ty => rw [Function.update_of_ne (by simp)]; rfl
  | out => rw [Function.update_of_ne (by simp)]; rfl

theorem upd_inp {M : FinTM2} (S : ∀ k, List (M.Γ k)) (i i' rx sx cy ty o : List Bool) :
    Function.update (mkStk S i rx sx cy ty o) .inp i' = mkStk S i' rx sx cy ty o := by
  funext k; cases k <;> rfl

theorem upd_rx {M : FinTM2} (S : ∀ k, List (M.Γ k)) (i rx rx' sx cy ty o : List Bool) :
    Function.update (mkStk S i rx sx cy ty o) .rx rx' = mkStk S i rx' sx cy ty o := by
  funext k; cases k <;> rfl

theorem upd_sx {M : FinTM2} (S : ∀ k, List (M.Γ k)) (i rx sx sx' cy ty o : List Bool) :
    Function.update (mkStk S i rx sx cy ty o) .sx sx' = mkStk S i rx sx' cy ty o := by
  funext k; cases k <;> rfl

theorem upd_cy {M : FinTM2} (S : ∀ k, List (M.Γ k)) (i rx sx cy cy' ty o : List Bool) :
    Function.update (mkStk S i rx sx cy ty o) .cy cy' = mkStk S i rx sx cy' ty o := by
  funext k; cases k <;> rfl

theorem upd_ty {M : FinTM2} (S : ∀ k, List (M.Γ k)) (i rx sx cy ty ty' o : List Bool) :
    Function.update (mkStk S i rx sx cy ty o) .ty ty' = mkStk S i rx sx cy ty' o := by
  funext k; cases k <;> rfl

theorem upd_out {M : FinTM2} (S : ∀ k, List (M.Γ k)) (i rx sx cy ty o o' : List Bool) :
    Function.update (mkStk S i rx sx cy ty o) .out o' = mkStk S i rx sx cy ty o' := by
  funext k; cases k <;> rfl

theorem initList_halfTM {f : List Bool → Bool}
    (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) (x : List Bool) :
    initList (halfTM c) x = (⟨some .init, initσ c.tm, mkStk (fun _ => []) x [] [] [] [] []⟩ : WCfg c.tm) := by
  unfold initList
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_halfTM {f : List Bool → Bool}
    (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f) (o : List Bool) :
    haltList (halfTM c) o = (⟨none, initσ c.tm, mkStk (fun _ => []) [] [] [] [] [] o⟩ : WCfg c.tm) := by
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

def embCfg {M : FinTM2} (acc : Bool) (rx cy : List Bool) (cfg : TM2.Cfg M.Γ M.Λ M.σ) : WCfg M :=
  ⟨some (cfg.l.elim .afterM .orig), (cfg.var, acc, false, none), mkStk cfg.stk [] rx [] cy [] []⟩

theorem simM_aux {M : FinTM2} (acc : Bool) (rx cy : List Bool)
    (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trM q) ((v, acc, false, none) : Wσ M) (mkStk S [] rx [] cy [] []) =
      embCfg acc rx cy (TM2.stepAux q v S) := by
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
    (acc : Bool) (rx cy : List Bool) (cfg cfg' : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ)
    (h : TM2.step c.tm.m cfg = some cfg') :
    TM2.step (wProg c) (embCfg acc rx cy cfg) = some (embCfg acc rx cy cfg') := by
  obtain ⟨l, v, S⟩ := cfg
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simM_aux acc rx cy (c.tm.m l) v S)

section steps

variable {f : List Bool → Bool}
variable (c : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f)

theorem loop_init (x rx cy : List Bool) :
    (flip bind (TM2.step (wProg c)))^[x.length + 1]
        (some (⟨some .init, initσ c.tm, mkStk (fun _ => []) x rx [] cy [] []⟩ : WCfg c.tm)) =
      some ⟨some .loadY, initσ c.tm,
        mkStk (fun _ => []) [] (x.reverse ++ rx) [] (List.replicate x.length false ++ cy) [] []⟩ := by
  induction x generalizing rx cy with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
      List.nil_append, List.replicate_zero]
    have hst : TM2.step (wProg c)
        (⟨some .init, initσ c.tm, mkStk (fun _ => []) [] rx [] cy [] []⟩ : WCfg c.tm) =
        some ⟨some .loadY, initσ c.tm, mkStk (fun _ => []) [] rx [] cy [] []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_inp]
    exact hst
  | cons a xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (wProg c)
        (⟨some .init, initσ c.tm, mkStk (fun _ => []) (a :: xs) rx [] cy [] []⟩ : WCfg c.tm) =
        some ⟨some .init, initσ c.tm, mkStk (fun _ => []) xs (a :: rx) [] (false :: cy) [] []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_inp, upd_rx, upd_cy]
      rfl
    have e : flip bind (TM2.step (wProg c))
        (some (⟨some .init, initσ c.tm, mkStk (fun _ => []) (a :: xs) rx [] cy [] []⟩ : WCfg c.tm)) =
        some ⟨some .init, initσ c.tm, mkStk (fun _ => []) xs (a :: rx) [] (false :: cy) [] []⟩ := hst
    rw [e, ih (a :: rx) (false :: cy)]
    have hrep : List.replicate xs.length false ++ false :: cy =
        List.replicate (xs.length + 1) false ++ cy := by
      rw [List.replicate_succ', List.append_assoc]
      rfl
    simp [hrep]

theorem loop_loadY (acc : Bool) (rx cy ty : List Bool) (s0 : List (c.tm.Γ c.tm.k₀)) :
    (flip bind (TM2.step (wProg c)))^[cy.length + 1]
        (some (⟨some .loadY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] cy ty []⟩ : WCfg c.tm)) =
      some ⟨some .restoreY, (c.tm.initialState, acc, false, none),
        mkStk (Function.update (fun _ => []) c.tm.k₀ (cy.reverse.map c.inputAlphabet.invFun ++ s0))
          [] rx [] [] (cy.reverse ++ ty) []⟩ := by
  induction cy generalizing ty s0 with
  | nil =>
    have hst : TM2.step (wProg c)
        (⟨some .loadY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] [] ty []⟩ : WCfg c.tm) =
        some ⟨some .restoreY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] [] ty []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_cy]
    exact hst
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (wProg c)
        (⟨some .loadY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] (b :: bs) ty []⟩ : WCfg c.tm) =
        some ⟨some .loadY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ (c.inputAlphabet.invFun b :: s0))
            [] rx [] bs (b :: ty) []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_cy, upd_ty, upd_orig]
      simp only [mkStk, Function.update_self, Function.update_idem]
    have e : flip bind (TM2.step (wProg c))
        (some (⟨some .loadY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] (b :: bs) ty []⟩ : WCfg c.tm)) =
        some ⟨some .loadY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ (c.inputAlphabet.invFun b :: s0))
            [] rx [] bs (b :: ty) []⟩ := hst
    rw [e, ih (b :: ty) (c.inputAlphabet.invFun b :: s0)]
    simp

theorem loop_restoreY (acc : Bool) (rx cy ty : List Bool) (s0 : List (c.tm.Γ c.tm.k₀)) :
    (flip bind (TM2.step (wProg c)))^[ty.length + 1]
        (some (⟨some .restoreY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] cy ty []⟩ : WCfg c.tm)) =
      some ⟨some .loadX, (c.tm.initialState, acc, false, none),
        mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] (ty.reverse ++ cy) [] []⟩ := by
  induction ty generalizing cy with
  | nil =>
    have hst : TM2.step (wProg c)
        (⟨some .restoreY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] cy [] []⟩ : WCfg c.tm) =
        some ⟨some .loadX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] cy [] []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_ty]
    exact hst
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (wProg c)
        (⟨some .restoreY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] cy (b :: bs) []⟩ : WCfg c.tm) =
        some ⟨some .restoreY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] (b :: cy) bs []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_ty, upd_cy]
      rfl
    have e : flip bind (TM2.step (wProg c))
        (some (⟨some .restoreY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] cy (b :: bs) []⟩ : WCfg c.tm)) =
        some ⟨some .restoreY, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] (b :: cy) bs []⟩ := hst
    rw [e, ih (b :: cy)]
    simp

theorem loop_loadX (acc : Bool) (rx sx cy : List Bool) (s0 : List (c.tm.Γ c.tm.k₀)) :
    (flip bind (TM2.step (wProg c)))^[rx.length + 1]
        (some (⟨some .loadX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx sx cy [] []⟩ : WCfg c.tm)) =
      some ⟨some .restoreX, (c.tm.initialState, acc, false, none),
        mkStk (Function.update (fun _ => []) c.tm.k₀ (rx.reverse.map c.inputAlphabet.invFun ++ s0))
          [] [] (rx.reverse ++ sx) cy [] []⟩ := by
  induction rx generalizing sx s0 with
  | nil =>
    have hst : TM2.step (wProg c)
        (⟨some .loadX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] [] sx cy [] []⟩ : WCfg c.tm) =
        some ⟨some .restoreX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] [] sx cy [] []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_rx]
    exact hst
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (wProg c)
        (⟨some .loadX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] (b :: bs) sx cy [] []⟩ : WCfg c.tm) =
        some ⟨some .loadX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ (c.inputAlphabet.invFun b :: s0))
            [] bs (b :: sx) cy [] []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_rx, upd_sx, upd_orig]
      simp only [mkStk, Function.update_self, Function.update_idem]
    have e : flip bind (TM2.step (wProg c))
        (some (⟨some .loadX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] (b :: bs) sx cy [] []⟩ : WCfg c.tm)) =
        some ⟨some .loadX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ (c.inputAlphabet.invFun b :: s0))
            [] bs (b :: sx) cy [] []⟩ := hst
    rw [e, ih (b :: sx) (c.inputAlphabet.invFun b :: s0)]
    simp

theorem loop_restoreX (acc : Bool) (rx sx cy : List Bool) (s0 : List (c.tm.Γ c.tm.k₀)) :
    (flip bind (TM2.step (wProg c)))^[sx.length + 1]
        (some (⟨some .restoreX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx sx cy [] []⟩ : WCfg c.tm)) =
      some ⟨some (.orig c.tm.main), (c.tm.initialState, acc, false, none),
        mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] (sx.reverse ++ rx) [] cy [] []⟩ := by
  induction sx generalizing rx with
  | nil =>
    have hst : TM2.step (wProg c)
        (⟨some .restoreX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] cy [] []⟩ : WCfg c.tm) =
        some ⟨some (.orig c.tm.main), (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx [] cy [] []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_sx]
    exact hst
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (wProg c)
        (⟨some .restoreX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx (b :: bs) cy [] []⟩ : WCfg c.tm) =
        some ⟨some .restoreX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] (b :: rx) bs cy [] []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_sx, upd_rx]
      rfl
    have e : flip bind (TM2.step (wProg c))
        (some (⟨some .restoreX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] rx (b :: bs) cy [] []⟩ : WCfg c.tm)) =
        some ⟨some .restoreX, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ s0) [] (b :: rx) bs cy [] []⟩ := hst
    rw [e, ih (b :: rx)]
    simp

theorem step_afterM (acc b : Bool) (rx cy : List Bool) :
    TM2.step (wProg c)
        (⟨some .afterM, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₁ [c.outputAlphabet.invFun b]) [] rx [] cy [] []⟩ : WCfg c.tm) =
      some ⟨some .inc, (c.tm.initialState, acc || b, true, none),
        mkStk (fun _ => []) [] rx [] cy [] []⟩ := by
  simp only [TM2.step, wProg, TM2.stepAux, mkStk, Function.update_self, List.head?_cons,
    List.tail_cons, Option.map_some]
  rw [upd_orig]
  have hclr : Function.update (Function.update (fun _ : c.tm.K => []) c.tm.k₁ [c.outputAlphabet.invFun b])
      c.tm.k₁ [] = fun _ => [] := by
    rw [Function.update_idem, Function.update_eq_self_iff]
  rw [hclr]
  simp

theorem loop_inc (acc carry : Bool) (rx cy ty : List Bool) :
    (flip bind (TM2.step (wProg c)))^[cy.length + 1]
        (some (⟨some .inc, (c.tm.initialState, acc, carry, none),
          mkStk (fun _ => []) [] rx [] cy ty []⟩ : WCfg c.tm)) =
      some ⟨some (if (incStep carry cy).1 then .drainTY else .unrevInc),
        (c.tm.initialState, acc, false, none),
        mkStk (fun _ => []) [] rx [] [] ((incStep carry cy).2.reverse ++ ty) []⟩ := by
  induction cy generalizing carry ty with
  | nil =>
    cases carry with
    | false =>
      have hst : TM2.step (wProg c)
          (⟨some .inc, (c.tm.initialState, acc, false, none),
            mkStk (fun _ => []) [] rx [] [] ty []⟩ : WCfg c.tm) =
          some ⟨some .unrevInc, (c.tm.initialState, acc, false, none),
            mkStk (fun _ => []) [] rx [] [] ty []⟩ := by
        simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
          Option.isSome_none, Bool.cond_false]
        rw [upd_cy]
      exact hst
    | true =>
      have hst : TM2.step (wProg c)
          (⟨some .inc, (c.tm.initialState, acc, true, none),
            mkStk (fun _ => []) [] rx [] [] ty []⟩ : WCfg c.tm) =
          some ⟨some .drainTY, (c.tm.initialState, acc, false, none),
            mkStk (fun _ => []) [] rx [] [] ty []⟩ := by
        simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
          Option.isSome_none, Bool.cond_false, Bool.cond_true]
        rw [upd_cy]
      exact hst
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (wProg c)
        (⟨some .inc, (c.tm.initialState, acc, carry, none),
          mkStk (fun _ => []) [] rx [] (b :: bs) ty []⟩ : WCfg c.tm) =
        some ⟨some .inc, (c.tm.initialState, acc, carry && b, none),
          mkStk (fun _ => []) [] rx [] bs (xor carry b :: ty) []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_cy, upd_ty]
      rfl
    have e : flip bind (TM2.step (wProg c))
        (some (⟨some .inc, (c.tm.initialState, acc, carry, none),
          mkStk (fun _ => []) [] rx [] (b :: bs) ty []⟩ : WCfg c.tm)) =
        some ⟨some .inc, (c.tm.initialState, acc, carry && b, none),
          mkStk (fun _ => []) [] rx [] bs (xor carry b :: ty) []⟩ := hst
    rw [e, ih (carry && b) (xor carry b :: ty)]
    simp only [incStep, List.reverse_cons, List.append_assoc, List.singleton_append]
    rfl

theorem loop_unrevInc (acc : Bool) (rx cy ty : List Bool) :
    (flip bind (TM2.step (wProg c)))^[ty.length + 1]
        (some (⟨some .unrevInc, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] cy ty []⟩ : WCfg c.tm)) =
      some ⟨some .loadY, (c.tm.initialState, acc, false, none),
        mkStk (fun _ => []) [] rx [] (ty.reverse ++ cy) [] []⟩ := by
  induction ty generalizing cy with
  | nil =>
    have hst : TM2.step (wProg c)
        (⟨some .unrevInc, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] cy [] []⟩ : WCfg c.tm) =
        some ⟨some .loadY, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] cy [] []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_ty]
    exact hst
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (wProg c)
        (⟨some .unrevInc, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] cy (b :: bs) []⟩ : WCfg c.tm) =
        some ⟨some .unrevInc, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] (b :: cy) bs []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true, Option.getD_some]
      rw [upd_ty, upd_cy]
      rfl
    have e : flip bind (TM2.step (wProg c))
        (some (⟨some .unrevInc, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] cy (b :: bs) []⟩ : WCfg c.tm)) =
        some ⟨some .unrevInc, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] (b :: cy) bs []⟩ := hst
    rw [e, ih (b :: cy)]
    simp

theorem loop_drainTY (acc : Bool) (rx ty : List Bool) :
    (flip bind (TM2.step (wProg c)))^[ty.length + 1]
        (some (⟨some .drainTY, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] [] ty []⟩ : WCfg c.tm)) =
      some ⟨some .drainRX, (c.tm.initialState, acc, false, none),
        mkStk (fun _ => []) [] rx [] [] [] []⟩ := by
  induction ty with
  | nil =>
    have hst : TM2.step (wProg c)
        (⟨some .drainTY, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] [] [] []⟩ : WCfg c.tm) =
        some ⟨some .drainRX, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] [] [] []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_ty]
    exact hst
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (wProg c)
        (⟨some .drainTY, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] [] (b :: bs) []⟩ : WCfg c.tm) =
        some ⟨some .drainTY, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] [] bs []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true]
      rw [upd_ty]
    have e : flip bind (TM2.step (wProg c))
        (some (⟨some .drainTY, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] [] (b :: bs) []⟩ : WCfg c.tm)) =
        some ⟨some .drainTY, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] [] bs []⟩ := hst
    rw [e, ih]

theorem loop_drainRX (acc : Bool) (rx : List Bool) :
    (flip bind (TM2.step (wProg c)))^[rx.length + 1]
        (some (⟨some .drainRX, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] rx [] [] [] []⟩ : WCfg c.tm)) =
      some ⟨none, initσ c.tm, mkStk (fun _ => []) [] [] [] [] [] [acc]⟩ := by
  induction rx with
  | nil =>
    have hst : TM2.step (wProg c)
        (⟨some .drainRX, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] [] [] [] [] []⟩ : WCfg c.tm) =
        some ⟨none, initσ c.tm, mkStk (fun _ => []) [] [] [] [] [] [acc]⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_nil, List.tail_nil,
        Option.isSome_none, Bool.cond_false]
      rw [upd_rx, upd_out]
      rfl
    exact hst
  | cons b bs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hst : TM2.step (wProg c)
        (⟨some .drainRX, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] (b :: bs) [] [] [] []⟩ : WCfg c.tm) =
        some ⟨some .drainRX, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] bs [] [] [] []⟩ := by
      simp only [TM2.step, wProg, TM2.stepAux, mkStk, List.head?_cons, List.tail_cons,
        Option.isSome_some, Bool.cond_true]
      rw [upd_rx]
    have e : flip bind (TM2.step (wProg c))
        (some (⟨some .drainRX, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] (b :: bs) [] [] [] []⟩ : WCfg c.tm)) =
        some ⟨some .drainRX, (c.tm.initialState, acc, false, none),
          mkStk (fun _ => []) [] bs [] [] [] []⟩ := hst
    rw [e, ih]

theorem run_one_iter (x cy : List Bool) (hlen : cy.length = x.length) (acc : Bool) :
    ∃ t : ℕ, t ≤ 5 * x.length + 6 + c.time (2 * x.length) ∧
      (flip bind (TM2.step (wProg c)))^[t]
          (some (⟨some .loadY, (c.tm.initialState, acc, false, none),
            mkStk (fun _ => []) [] x.reverse [] cy [] []⟩ : WCfg c.tm)) =
        some ⟨some (if (incStep true cy).1 then .drainTY else .unrevInc),
          (c.tm.initialState, acc || f (x ++ cy.reverse), false, none),
          mkStk (fun _ => []) [] x.reverse [] [] (incStep true cy).2.reverse []⟩ := by
  let z : List Bool := x ++ cy.reverse
  have hzlen : z.length = 2 * x.length := by
    simp only [z, List.length_append, List.length_reverse, hlen]
    omega
  let outM := c.outputsFun z
  have hsteps_le : outM.steps ≤ c.time (2 * x.length) := by
    have henc : (PvsNP.encodeString z).length = 2 * x.length := by
      simpa [PvsNP.encodeString, Computability.encodingList] using hzlen
    exact outM.steps_le_m.trans (le_of_eq (congrArg c.time henc))
  have hrunM :
      (flip bind (TM2.step (wProg c)))^[outM.steps]
          (some (⟨some (.orig c.tm.main), (c.tm.initialState, acc, false, none),
            mkStk (Function.update (fun _ => []) c.tm.k₀ (z.map c.inputAlphabet.invFun))
              [] x.reverse [] cy [] []⟩ : WCfg c.tm)) =
        some ⟨some .afterM, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₁ [c.outputAlphabet.invFun (f z)])
            [] x.reverse [] cy [] []⟩ := by
    have hev : (flip bind (TM2.step c.tm.m))^[outM.steps]
        (some (initList c.tm (z.map c.inputAlphabet.invFun))) =
        some (haltList c.tm [c.outputAlphabet.invFun (f z)]) := outM.evals_in_steps
    have hsim := simulate_run (TM2.step c.tm.m) (TM2.step (wProg c))
      (embCfg acc x.reverse cy) (step_simM c acc x.reverse cy) outM.steps
      (initList c.tm (z.map c.inputAlphabet.invFun))
      (haltList c.tm [c.outputAlphabet.invFun (f z)]) hev
    have hinitE : embCfg acc x.reverse cy (initList c.tm (z.map c.inputAlphabet.invFun)) =
        ⟨some (.orig c.tm.main), (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₀ (z.map c.inputAlphabet.invFun))
            [] x.reverse [] cy [] []⟩ := by
      rw [initList_orig]; rfl
    have hhaltE : embCfg acc x.reverse cy (haltList c.tm [c.outputAlphabet.invFun (f z)]) =
        ⟨some .afterM, (c.tm.initialState, acc, false, none),
          mkStk (Function.update (fun _ => []) c.tm.k₁ [c.outputAlphabet.invFun (f z)])
            [] x.reverse [] cy [] []⟩ := by
      rw [haltList_orig]; rfl
    rw [hinitE, hhaltE] at hsim
    exact hsim
  let t : ℕ := (cy.length + 1) + 1 + outM.steps + (x.length + 1) + (x.length + 1) +
    (cy.length + 1) + (cy.length + 1)
  refine ⟨t, by dsimp only [t]; omega, ?_⟩
  dsimp only [t]
  have hupd0 : Function.update (fun k : c.tm.K => ([] : List (c.tm.Γ k))) c.tm.k₀ [] =
      (fun k : c.tm.K => ([] : List (c.tm.Γ k))) := by
    funext k
    by_cases h : k = c.tm.k₀
    · subst h; simp
    · simp [h]
  rw [← hupd0]
  rw [Function.iterate_add_apply, loop_loadY c acc x.reverse cy [] []]
  rw [List.append_nil, List.append_nil]
  rw [Function.iterate_add_apply]
  have hry := loop_restoreY c acc x.reverse [] cy.reverse (cy.reverse.map c.inputAlphabet.invFun)
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at hry
  rw [hry]
  rw [Function.iterate_add_apply]
  have hlx := loop_loadX c acc x.reverse [] cy (cy.reverse.map c.inputAlphabet.invFun)
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at hlx
  rw [hlx]
  rw [Function.iterate_add_apply]
  have hrx := loop_restoreX c acc [] x cy
    (x.map c.inputAlphabet.invFun ++ cy.reverse.map c.inputAlphabet.invFun)
  rw [List.append_nil] at hrx
  rw [hrx]
  rw [Function.iterate_add_apply]
  have hzmap : x.map c.inputAlphabet.invFun ++ cy.reverse.map c.inputAlphabet.invFun =
      z.map c.inputAlphabet.invFun := by
    simp [z]
  rw [hzmap, hrunM]
  rw [Function.iterate_add_apply]
  have hafter : (flip bind (TM2.step (wProg c)))^[1]
      (some (⟨some .afterM, (c.tm.initialState, acc, false, none),
        mkStk (Function.update (fun _ => []) c.tm.k₁ [c.outputAlphabet.invFun (f z)])
          [] x.reverse [] cy [] []⟩ : WCfg c.tm)) =
      some ⟨some .inc, (c.tm.initialState, acc || f z, true, none),
        mkStk (fun _ => []) [] x.reverse [] cy [] []⟩ :=
    step_afterM c acc (f z) x.reverse cy
  rw [hafter]
  have hinc := loop_inc c (acc || f z) true x.reverse cy []
  rw [List.append_nil] at hinc
  rw [hupd0]
  exact hinc

theorem loop_search (x : List Bool) :
    ∀ (m : ℕ) (cy : List Bool) (acc : Bool),
      cy.length = x.length →
      Nat.ofDigits (2 : ℕ) (cy.map Bool.toNat) + m = 2 ^ x.length →
      1 ≤ m →
      ∃ (t : ℕ) (res : Bool) (tyf : List Bool),
        t ≤ m * (6 * x.length + 7 + c.time (2 * x.length)) ∧
        tyf.length = x.length ∧
        (res = true ↔ acc = true ∨
          ∃ y : List Bool, y.length = x.length ∧
            Nat.ofDigits (2 : ℕ) (cy.map Bool.toNat) ≤ Nat.ofDigits (2 : ℕ) (y.reverse.map Bool.toNat) ∧
            f (x ++ y) = true) ∧
        (flip bind (TM2.step (wProg c)))^[t]
            (some (⟨some .loadY, (c.tm.initialState, acc, false, none),
              mkStk (fun _ => []) [] x.reverse [] cy [] []⟩ : WCfg c.tm)) =
          some ⟨some .drainTY, (c.tm.initialState, res, false, none),
            mkStk (fun _ => []) [] x.reverse [] [] tyf []⟩ := by
  intro m
  induction m with
  | zero => intro _ _ _ _ hm; omega
  | succ m' ih =>
    intro cy acc hlen hsum _
    obtain ⟨t1, ht1, hrun1⟩ := run_one_iter c x cy hlen acc
    have hincVal := incStep_val true cy
    have hincLen := incStep_len true cy
    have hincLt := ofDigits_bool_lt (incStep true cy).2
    rw [hincLen, hlen] at hincLt
    rw [hlen, Bool.toNat_true] at hincVal
    cases m' with
    | zero =>
      have hov : (incStep true cy).1 = true := by
        cases h1 : (incStep true cy).1 with
        | true => rfl
        | false =>
          rw [h1, Bool.toNat_false, zero_mul, Nat.add_zero] at hincVal
          omega
      rw [hov] at hrun1
      simp only [↓reduceIte] at hrun1
      refine ⟨t1, acc || f (x ++ cy.reverse), (incStep true cy).2.reverse, ?_, ?_, ?_, hrun1⟩
      · simp only [Nat.zero_add, one_mul]; omega
      · simp [hincLen, hlen]
      · constructor
        · intro hres
          rcases Bool.or_eq_true_iff.mp hres with ha | hf
          · exact Or.inl ha
          · right
            exact ⟨cy.reverse, by simp [hlen], by simp, hf⟩
        · rintro (ha | ⟨y, hyl, hge, hfy⟩)
          · simp [ha]
          · have hylt := ofDigits_bool_lt y.reverse
            simp only [List.length_reverse, hyl] at hylt
            have heqDig : Nat.ofDigits (2 : ℕ) (cy.map Bool.toNat) =
                Nat.ofDigits (2 : ℕ) (y.reverse.map Bool.toNat) := by omega
            have hcyy : cy = y.reverse :=
              ofDigits_bool_inj (by simp [hlen, hyl]) heqDig
            have hycy : cy.reverse = y := by rw [hcyy, List.reverse_reverse]
            rw [hycy]
            simp [hfy]
    | succ m'' =>
      have hov : (incStep true cy).1 = false := by
        cases h1 : (incStep true cy).1 with
        | false => rfl
        | true =>
          rw [h1, Bool.toNat_true, one_mul] at hincVal
          omega
      rw [hov] at hrun1
      simp only [Bool.false_eq_true, ↓reduceIte] at hrun1
      rw [hov, Bool.toNat_false, zero_mul, Nat.add_zero] at hincVal
      let cy' : List Bool := (incStep true cy).2
      have hcy'len : cy'.length = x.length := by rw [hincLen, hlen]
      have hcy'sum : Nat.ofDigits (2 : ℕ) (cy'.map Bool.toNat) + (m'' + 1) = 2 ^ x.length := by
        dsimp only [cy']
        omega
      obtain ⟨t2, res, tyf, ht2, htyflen, hresIff, hrun2⟩ :=
        ih cy' (acc || f (x ++ cy.reverse)) hcy'len hcy'sum (by omega)
      refine ⟨t2 + (x.length + 1) + t1, res, tyf, ?_, htyflen, ?_, ?_⟩
      · have hmul : (m'' + 1 + 1) * (6 * x.length + 7 + c.time (2 * x.length)) =
            (m'' + 1) * (6 * x.length + 7 + c.time (2 * x.length)) +
              (6 * x.length + 7 + c.time (2 * x.length)) := by ring
        omega
      · rw [hresIff]
        constructor
        · rintro (hacc1 | ⟨y, hyl, hge, hfy⟩)
          · rcases Bool.or_eq_true_iff.mp hacc1 with ha | hf
            · exact Or.inl ha
            · right; exact ⟨cy.reverse, by simp [hlen], by simp, hf⟩
          · right
            refine ⟨y, hyl, ?_, hfy⟩
            dsimp only [cy'] at hge
            omega
        · rintro (ha | ⟨y, hyl, hge, hfy⟩)
          · left; simp [ha]
          · by_cases heqDig : Nat.ofDigits (2 : ℕ) (cy.map Bool.toNat) =
                Nat.ofDigits (2 : ℕ) (y.reverse.map Bool.toNat)
            · have hcyy : cy = y.reverse :=
                ofDigits_bool_inj (by simp [hlen, hyl]) heqDig
              have hycy : cy.reverse = y := by rw [hcyy, List.reverse_reverse]
              left
              rw [hycy]
              simp [hfy]
            · right
              refine ⟨y, hyl, ?_, hfy⟩
              dsimp only [cy']
              omega
      · rw [Function.iterate_add_apply, hrun1, Function.iterate_add_apply]
        have hunr := loop_unrevInc c (acc || f (x ++ cy.reverse)) x.reverse [] cy'.reverse
        rw [List.length_reverse, hcy'len, List.reverse_reverse, List.append_nil] at hunr
        rw [hunr]
        exact hrun2

end steps

theorem tc_exp_half_aux (L : Language Bool) :
    (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
    ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
        (∀ x : List Bool, (∃ y : List Bool, y.length = x.length ∧ x ++ y ∈ L) ↔ f x = true) ∧
          ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  classical
  rintro ⟨k, f, c, hdec, htime⟩
  let fH : List Bool → Bool := fun x => decide (∃ y : List Bool, y.length = x.length ∧ x ++ y ∈ L)
  have hfH : ∀ x : List Bool, (∃ y : List Bool, y.length = x.length ∧ x ++ y ∈ L) ↔ fH x = true := by
    intro x
    simp [fH]
  obtain ⟨p, hp⟩ := half_time_le_exp_poly k
  obtain ⟨K, hK⟩ := exp_poly_bound p
  have hrun : ∀ x : List Bool,
      ∃ t : ℕ, t ≤ 2 ^ (x.length ^ K) + K ∧
        (flip bind (TM2.step (wProg c)))^[t] (some (initList (halfTM c) x)) =
          some (haltList (halfTM c) [fH x]) := by
    intro x
    let cy0 : List Bool := List.replicate x.length false
    have hcy0len : cy0.length = x.length := List.length_replicate
    have hcy0val : Nat.ofDigits (2 : ℕ) (cy0.map Bool.toNat) = 0 := ofDigits_replicate_false x.length
    have hpos : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
    obtain ⟨ts, res, tyf, hts, htyflen, hresIff, hsearch⟩ :=
      loop_search c x (2 ^ x.length) cy0 false hcy0len (by omega) hpos
    have hres_eq : res = fH x := by
      apply Bool.eq_iff_iff.mpr
      rw [hresIff, ← hfH x]
      constructor
      · rintro (hfalse | ⟨y, hyl, _, hfy⟩)
        · exact absurd hfalse (by decide)
        · exact ⟨y, hyl, (hdec (x ++ y)).mpr hfy⟩
      · rintro ⟨y, hyl, hxyL⟩
        right
        exact ⟨y, hyl, by omega, (hdec (x ++ y)).mp hxyL⟩
    let t : ℕ := (x.length + 1) + (x.length + 1) + ts + (x.length + 1)
    have ht_le : t ≤ 2 ^ (x.length ^ K) + K := by
      have hct : c.time (2 * x.length) ≤ 2 ^ ((2 * x.length) ^ k) + k := htime (2 * x.length)
      have hts' : ts ≤ 2 ^ x.length * (6 * x.length + 7 + (2 ^ ((2 * x.length) ^ k) + k)) := by
        calc ts ≤ 2 ^ x.length * (6 * x.length + 7 + c.time (2 * x.length)) := hts
          _ ≤ 2 ^ x.length * (6 * x.length + 7 + (2 ^ ((2 * x.length) ^ k) + k)) :=
              Nat.mul_le_mul_left _ (by omega)
      have h1 : t ≤ (x.length + 1) + 2 ^ x.length * (6 * x.length + 7 + (2 ^ ((2 * x.length) ^ k) + k)) +
          (2 * x.length + 2) := by
        dsimp only [t]
        omega
      exact h1.trans ((hp x.length).trans (hK x.length))
    refine ⟨t, ht_le, ?_⟩
    refine (congrArg (fun cfg => (flip bind (TM2.step (wProg c)))^[t] (some cfg))
      (initList_halfTM c x)).trans
      (Eq.trans ?_ (congrArg some (haltList_halfTM c [fH x])).symm)
    dsimp only [t]
    rw [Function.iterate_add_apply]
    have hinit := loop_init c x [] []
    rw [List.append_nil, List.append_nil] at hinit
    rw [hinit, Function.iterate_add_apply]
    change (flip bind (TM2.step (wProg c)))^[ts]
        (some (⟨some .loadY, initσ c.tm,
          mkStk (fun _ => []) [] x.reverse [] (List.replicate x.length false) [] []⟩ : WCfg c.tm)) =
      some ⟨some .drainTY, (c.tm.initialState, res, false, none),
        mkStk (fun _ => []) [] x.reverse [] [] tyf []⟩ at hsearch
    rw [hsearch, Function.iterate_add_apply]
    have hdty := loop_drainTY c res x.reverse tyf
    rw [htyflen] at hdty
    rw [hdty]
    have hdrx := loop_drainRX c res x.reverse
    rw [List.length_reverse] at hdrx
    rw [hdrx, hres_eq]
    rfl
  let M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer fH :=
    { tm := halfTM c
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
            have hm2 : List.map (Equiv.refl Bool).invFun (PvsNP.encodeAnswer (fH x)) = [fH x] := by
              simp [PvsNP.encodeAnswer, Computability.encodeBool]
            exact (congrArg (fun i => (flip bind (TM2.step (wProg c)))^[Classical.choose h]
              (some (initList (halfTM c) i))) hm1).trans
              (hspec.2.trans (congrArg (fun o => some (haltList (halfTM c) o)) hm2.symm))
          steps_le_m := by
            have hspec := Classical.choose_spec h
            have hlen : (PvsNP.encodeString x).length = x.length := by
              simp [PvsNP.encodeString, Computability.encodingList]
            rw [hlen]
            exact hspec.1 } }
  exact ⟨K, fH, M, hfH, fun _ => le_refl _⟩

end PvsNP.Units.tc_exp_half

/-- Exponential time is closed under taking first halves (TM2). -/
theorem PvsNP.Units.tc_exp_half :
    ∀ L : Language Bool,
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
          (∀ x : List Bool, (∃ y : List Bool, y.length = x.length ∧ x ++ y ∈ L) ↔ f x = true) ∧
            ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k :=
  PvsNP.Units.tc_exp_half.tc_exp_half_aux
