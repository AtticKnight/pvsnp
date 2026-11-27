import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.tl_lang_val_pow2_p

open Turing

/-- Internal automaton state tracking how many `true` bits have been seen: 0, 1, or ≥2. -/
inductive St : Type
  | zero | one | many
  deriving DecidableEq

instance : Fintype St where
  elems := { St.zero, St.one, St.many }
  complete x := by cases x <;> simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

def trans (s : St) (b : Bool) : St :=
  match b with
  | false => s
  | true =>
    match s with
    | .zero => .one
    | .one => .many
    | .many => .many

def runSt : St → List Bool → St
  | s, [] => s
  | s, b :: x => runSt (trans s b) x

def acceptSt : St → Bool
  | .one => true
  | _ => false

theorem runSt_many (x : List Bool) : runSt .many x = .many := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> exact ih

theorem runSt_one_iff (x : List Bool) : runSt .one x = .one ↔ x.count true = 0 := by
  induction x with
  | nil => simp only [runSt, List.count_nil]
  | cons b x ih =>
    cases b with
    | false =>
      have hcf : (false :: x).count true = x.count true := by
        rw [List.count_cons]; exact Nat.add_zero _
      rw [hcf]
      exact ih
    | true =>
      have hct : (true :: x).count true = x.count true + 1 := by
        rw [List.count_cons]; rfl
      rw [hct]
      show runSt .many x = .one ↔ x.count true + 1 = 0
      rw [runSt_many]
      constructor
      · intro h; cases h
      · intro h; omega

theorem runSt_zero_iff (x : List Bool) : runSt .zero x = .one ↔ x.count true = 1 := by
  induction x with
  | nil =>
    simp only [runSt, List.count_nil]
    constructor
    · intro h; cases h
    · intro h; omega
  | cons b x ih =>
    cases b with
    | false =>
      have hcf : (false :: x).count true = x.count true := by
        rw [List.count_cons]; exact Nat.add_zero _
      rw [hcf]
      exact ih
    | true =>
      have hct : (true :: x).count true = x.count true + 1 := by
        rw [List.count_cons]; rfl
      rw [hct]
      show runSt .one x = .one ↔ x.count true + 1 = 1
      rw [runSt_one_iff]
      omega

theorem acceptSt_eq_true (s : St) : acceptSt s = true ↔ s = .one := by
  cases s <;> simp only [acceptSt, reduceCtorEq, Bool.false_eq_true]

theorem ofDigits_eq_zero_iff (x : List Bool) :
    Nat.ofDigits 2 (x.map Bool.toNat) = 0 ↔ x.count true = 0 := by
  induction x with
  | nil => simp only [List.map_nil, Nat.ofDigits_nil, List.count_nil]
  | cons b x ih =>
    cases b with
    | false =>
      have hcf : (false :: x).count true = x.count true := by
        rw [List.count_cons]; exact Nat.add_zero _
      rw [hcf]
      simp only [List.map_cons, Bool.toNat_false, Nat.ofDigits_cons, Nat.zero_add,
        Nat.mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact ih
    | true =>
      have hct : (true :: x).count true = x.count true + 1 := by
        rw [List.count_cons]; rfl
      rw [hct]
      simp only [List.map_cons, Bool.toNat_true, Nat.ofDigits_cons]
      constructor
      · intro h; omega
      · intro h; omega

theorem ofDigits_eq_pow2_iff (x : List Bool) :
    (∃ k : ℕ, Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = 2 ^ k) ↔ x.count true = 1 := by
  induction x with
  | nil =>
    simp only [List.map_nil, Nat.ofDigits_nil, List.count_nil]
    constructor
    · rintro ⟨k, hk⟩
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      omega
    · intro h; omega
  | cons b x ih =>
    cases b with
    | false =>
      have hcf : (false :: x).count true = x.count true := by
        rw [List.count_cons]; exact Nat.add_zero _
      rw [hcf]
      simp only [List.map_cons, Bool.toNat_false, Nat.ofDigits_cons, Nat.zero_add]
      rw [← ih]
      constructor
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp only [Nat.pow_zero] at hk; omega
        | succ k' =>
          rw [Nat.pow_succ, Nat.mul_comm] at hk
          exact ⟨k', by omega⟩
      · rintro ⟨k, hk⟩
        exact ⟨k + 1, by rw [hk, Nat.pow_succ, Nat.mul_comm]⟩
    | true =>
      have hct : (true :: x).count true = x.count true + 1 := by
        rw [List.count_cons]; rfl
      rw [hct]
      simp only [List.map_cons, Bool.toNat_true, Nat.ofDigits_cons]
      constructor
      · rintro ⟨k, hk⟩
        cases k with
        | zero =>
          simp only [Nat.pow_zero] at hk
          have h0 : Nat.ofDigits 2 (x.map Bool.toNat) = 0 := by omega
          have hc0 := (ofDigits_eq_zero_iff x).mp h0
          omega
        | succ k' =>
          rw [Nat.pow_succ] at hk
          omega
      · intro h
        have hc0 : x.count true = 0 := by omega
        have h0 := (ofDigits_eq_zero_iff x).mpr hc0
        exact ⟨0, by rw [h0]; rfl⟩

/-- Single-stack TM2 statement: pop next bit, update `(hasBit, st)`; on empty stack push answer and halt. -/
def pow2Prog : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit (Bool × St) :=
  fun _ =>
    .pop () (fun s o => match o with
      | none => (false, s.2)
      | some b => (true, trans s.2 b))
      (.branch (fun s => s.1)
        (.load (fun s => (false, s.2)) (.goto fun _ => ()))
        (.push () (fun s => acceptSt s.2) (.load (fun _ => (false, .zero)) .halt)))

def pow2TM : FinTM2 :=
  { K := Unit
    k₀ := ()
    k₁ := ()
    Γ := fun _ => Bool
    Λ := Unit
    main := ()
    σ := Bool × St
    initialState := (false, .zero)
    Γk₀Fin := inferInstance
    m := pow2Prog }

abbrev Cfg := TM2.Cfg (fun _ : Unit => Bool) Unit (Bool × St)

theorem upd_unit (a a' : List Bool) :
    Function.update (fun _ : Unit => a) () a' = (fun _ : Unit => a') := by
  funext k; cases k; rfl

theorem initList_eq (x : List Bool) :
    (initList pow2TM x : Cfg) = ⟨some (), (false, .zero), fun _ => x⟩ := by
  unfold initList
  congr 1

theorem haltList_eq (y : List Bool) :
    (haltList pow2TM y : Cfg) = ⟨none, (false, .zero), fun _ => y⟩ := by
  unfold haltList
  congr 1

theorem step_cons (b : Bool) (x : List Bool) (s : St) :
    TM2.step pow2Prog (⟨some (), (false, s), fun _ => b :: x⟩ : Cfg) =
      some ⟨some (), (false, trans s b), fun _ => x⟩ := by
  simp only [TM2.step, pow2Prog, TM2.stepAux, upd_unit, List.head?_cons, List.tail_cons,
    Bool.cond_true]

theorem step_nil (s : St) :
    TM2.step pow2Prog (⟨some (), (false, s), fun _ => []⟩ : Cfg) =
      some ⟨none, (false, .zero), fun _ => [acceptSt s]⟩ := by
  simp only [TM2.step, pow2Prog, TM2.stepAux, upd_unit, List.head?_nil, List.tail_nil,
    Bool.cond_false]

theorem pow2_loop : ∀ (x : List Bool) (s : St),
    (flip bind (TM2.step pow2Prog))^[x.length + 1]
        (some (⟨some (), (false, s), fun _ => x⟩ : Cfg)) =
      some ⟨none, (false, .zero), fun _ => [acceptSt (runSt s x)]⟩ := by
  intro x
  induction x with
  | nil =>
    intro s
    exact step_nil s
  | cons b x ih =>
    intro s
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : flip bind (TM2.step pow2Prog)
        (some (⟨some (), (false, s), fun _ => b :: x⟩ : Cfg)) =
        some ⟨some (), (false, trans s b), fun _ => x⟩ :=
      step_cons b x s
    rw [hstep]
    exact ih (trans s b)

def inEquiv : pow2TM.Γ pow2TM.k₀ ≃ Bool := Equiv.refl Bool

def outEquiv : pow2TM.Γ pow2TM.k₁ ≃ Bool := Equiv.refl Bool

def decFn (x : List Bool) : Bool := acceptSt (runSt .zero x)

noncomputable def pow2_outputs (x : List Bool) :
    TM2OutputsInTime pow2TM
      (List.map inEquiv.invFun (PvsNP.encodeString x))
      (some (List.map outEquiv.invFun (PvsNP.encodeAnswer (decFn x))))
      ((Polynomial.X + Polynomial.C 1).eval (PvsNP.encodeString x).length) :=
  { steps := x.length + 1
    evals_in_steps := by
      have h1 : List.map inEquiv.invFun (PvsNP.encodeString x) = x := List.map_id x
      have h2 : List.map outEquiv.invFun (PvsNP.encodeAnswer (decFn x)) = [decFn x] := rfl
      show (flip bind (TM2.step pow2Prog))^[x.length + 1]
          (some (initList pow2TM (List.map inEquiv.invFun (PvsNP.encodeString x)) : Cfg)) =
        some (haltList pow2TM (List.map outEquiv.invFun (PvsNP.encodeAnswer (decFn x))) : Cfg)
      rw [h1, h2, initList_eq, haltList_eq]
      exact pow2_loop x .zero
    steps_le_m := by
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
        PvsNP.encodeString, Computability.encodingList, id_eq]
      exact le_refl _ }

end PvsNP.Units.tl_lang_val_pow2_p

theorem PvsNP.Units.tl_lang_val_pow2_p :
    ({x : List Bool | ∃ k : ℕ, Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = 2 ^ k} : Language Bool) ∈ PvsNP.P :=
  ⟨PvsNP.Units.tl_lang_val_pow2_p.decFn,
    ⟨{ tm := PvsNP.Units.tl_lang_val_pow2_p.pow2TM
       inputAlphabet := PvsNP.Units.tl_lang_val_pow2_p.inEquiv
       outputAlphabet := PvsNP.Units.tl_lang_val_pow2_p.outEquiv
       time := Polynomial.X + Polynomial.C 1
       outputsFun := PvsNP.Units.tl_lang_val_pow2_p.pow2_outputs }⟩,
    fun x => by
      show (∃ k : ℕ, Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) = 2 ^ k) ↔
        PvsNP.Units.tl_lang_val_pow2_p.acceptSt (PvsNP.Units.tl_lang_val_pow2_p.runSt .zero x) = true
      rw [PvsNP.Units.tl_lang_val_pow2_p.acceptSt_eq_true,
        PvsNP.Units.tl_lang_val_pow2_p.runSt_zero_iff,
        PvsNP.Units.tl_lang_val_pow2_p.ofDigits_eq_pow2_iff]⟩
