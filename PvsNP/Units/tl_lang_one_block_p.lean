import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

namespace PvsNP.Units.tl_lang_one_block_p

/-- The four phases of the one-block DFA: leading falses, the true block,
trailing falses, and the dead state. -/
inductive St
  | s0 | s1 | s2 | s3
  deriving DecidableEq

instance : Fintype St where
  elems := {St.s0, St.s1, St.s2, St.s3}
  complete := by
    intro x
    cases x <;> simp

/-- Transition of the one-block DFA. -/
def δ : St → Bool → St
  | .s0, false => .s0
  | .s0, true => .s1
  | .s1, false => .s2
  | .s1, true => .s1
  | .s2, false => .s2
  | .s2, true => .s3
  | .s3, false => .s3
  | .s3, true => .s3

/-- Accept unless dead. -/
def F : St → Bool
  | .s0 => true
  | .s1 => true
  | .s2 => true
  | .s3 => false

/-- Strings of the form `0^a 1^b 0^c`. -/
def L0 (x : List Bool) : Prop :=
  ∃ a b c, x = List.replicate a false ++ List.replicate b true ++ List.replicate c false

/-- Strings of the form `1^b 0^c`. -/
def L1 (x : List Bool) : Prop :=
  ∃ b c, x = List.replicate b true ++ List.replicate c false

/-- Strings of the form `0^c`. -/
def L2 (x : List Bool) : Prop :=
  ∃ c, x = List.replicate c false

/-- The dead state is absorbing. -/
theorem foldl_s3 (y : List Bool) : y.foldl δ St.s3 = St.s3 := by
  induction y with
  | nil => rfl
  | cons b y ih =>
    have h : δ St.s3 b = St.s3 := by cases b <;> rfl
    rw [List.foldl_cons, h]
    exact ih

theorem cons_false_L0 {y : List Bool} : L0 (false :: y) ↔ L0 y := by
  constructor
  · rintro ⟨a, b, c, h⟩
    cases a with
    | zero =>
      cases b with
      | zero =>
        cases c with
        | zero => simp [List.replicate_succ] at h
        | succ k =>
          have hy : y = List.replicate k false := by
            have h2 := h
            simp only [List.replicate_zero, List.nil_append, List.replicate_succ] at h2
            exact (List.cons.inj h2).2
          exact ⟨k, 0, 0, by simpa using hy⟩
      | succ m => simp [List.replicate_succ] at h
    | succ n =>
      have hy : y = List.replicate n false ++ List.replicate b true ++ List.replicate c false := by
        have h2 := h
        simp only [List.replicate_succ, List.cons_append] at h2
        exact (List.cons.inj h2).2
      exact ⟨n, b, c, hy⟩
  · rintro ⟨a, b, c, h⟩
    exact ⟨a + 1, b, c, by rw [h]; simp [List.replicate_succ, List.cons_append]⟩

theorem cons_true_L0 {y : List Bool} : L0 (true :: y) ↔ L1 y := by
  constructor
  · rintro ⟨a, b, c, h⟩
    cases a with
    | zero =>
      cases b with
      | zero =>
        cases c with
        | zero => simp [List.replicate_succ] at h
        | succ k => simp [List.replicate_succ] at h
      | succ m =>
        have hy : y = List.replicate m true ++ List.replicate c false := by
          have h2 := h
          simp only [List.replicate_zero, List.nil_append, List.replicate_succ,
            List.cons_append] at h2
          exact (List.cons.inj h2).2
        exact ⟨m, c, hy⟩
    | succ n => simp [List.replicate_succ] at h
  · rintro ⟨b, c, h⟩
    exact ⟨0, b + 1, c, by rw [h]; simp [List.replicate_succ, List.cons_append]⟩

theorem cons_false_L1 {y : List Bool} : L1 (false :: y) ↔ L2 y := by
  constructor
  · rintro ⟨b, c, h⟩
    cases b with
    | zero =>
      cases c with
      | zero => simp [List.replicate_succ] at h
      | succ k =>
        have hy : y = List.replicate k false := by
          have h2 := h
          simp only [List.replicate_zero, List.nil_append, List.replicate_succ] at h2
          exact (List.cons.inj h2).2
        exact ⟨k, by simpa using hy⟩
    | succ m => simp [List.replicate_succ] at h
  · rintro ⟨c, h⟩
    exact ⟨0, c + 1, by rw [h]; simp [List.replicate_succ, List.cons_append]⟩

theorem cons_true_L1 {y : List Bool} : L1 (true :: y) ↔ L1 y := by
  constructor
  · rintro ⟨b, c, h⟩
    cases b with
    | zero =>
      cases c with
      | zero => simp [List.replicate_succ] at h
      | succ k => simp [List.replicate_succ] at h
    | succ m =>
      have hy : y = List.replicate m true ++ List.replicate c false := by
        have h2 := h
        simp only [List.replicate_succ, List.cons_append] at h2
        exact (List.cons.inj h2).2
      exact ⟨m, c, hy⟩
  · rintro ⟨b, c, h⟩
    exact ⟨b + 1, c, by rw [h]; simp [List.replicate_succ, List.cons_append]⟩

theorem cons_false_L2 {y : List Bool} : L2 (false :: y) ↔ L2 y := by
  constructor
  · rintro ⟨c, h⟩
    cases c with
    | zero => simp [List.replicate_succ] at h
    | succ k =>
      have hy : y = List.replicate k false := by
        have h2 := h
        simp only [List.replicate_succ] at h2
        exact (List.cons.inj h2).2
      exact ⟨k, hy⟩
  · rintro ⟨c, h⟩
    exact ⟨c + 1, by rw [h]; simp [List.replicate_succ]⟩

theorem cons_true_L2 {y : List Bool} : L2 (true :: y) ↔ False := by
  constructor
  · rintro ⟨c, h⟩
    cases c with
    | zero => simp [List.replicate_succ] at h
    | succ k => simp [List.replicate_succ] at h
  · intro h
    exact h.elim

/-- The DFA accepts exactly the one-block strings, from each phase. -/
theorem correct (x : List Bool) :
    (F (x.foldl δ St.s0) = true ↔ L0 x) ∧
    (F (x.foldl δ St.s1) = true ↔ L1 x) ∧
    (F (x.foldl δ St.s2) = true ↔ L2 x) := by
  induction x with
  | nil =>
    simp only [List.foldl_nil]
    refine ⟨⟨fun _ => ⟨0, 0, 0, by simp⟩, fun _ => rfl⟩,
            ⟨fun _ => ⟨0, 0, by simp⟩, fun _ => rfl⟩,
            ⟨fun _ => ⟨0, by simp⟩, fun _ => rfl⟩⟩
  | cons b y ih =>
    obtain ⟨ih0, ih1, ih2⟩ := ih
    cases b with
    | false =>
      simp only [List.foldl_cons]
      refine ⟨?_, ?_, ?_⟩
      · rw [show δ St.s0 false = St.s0 from rfl]
        exact ih0.trans cons_false_L0.symm
      · rw [show δ St.s1 false = St.s2 from rfl]
        exact ih2.trans cons_false_L1.symm
      · rw [show δ St.s2 false = St.s2 from rfl]
        exact ih2.trans cons_false_L2.symm
    | true =>
      simp only [List.foldl_cons]
      refine ⟨?_, ?_, ?_⟩
      · rw [show δ St.s0 true = St.s1 from rfl]
        exact ih1.trans cons_true_L0.symm
      · rw [show δ St.s1 true = St.s1 from rfl]
        exact ih1.trans cons_true_L1.symm
      · rw [show δ St.s2 true = St.s3 from rfl, foldl_s3,
            show F St.s3 = false from rfl]
        simp [cons_true_L2]

end PvsNP.Units.tl_lang_one_block_p

open PvsNP.Units.tl_lang_one_block_p

theorem PvsNP.Units.tl_lang_one_block_p :
    ({x : List Bool | ∃ a b c : ℕ, x = List.replicate a false ++ List.replicate b true ++ List.replicate c false} : Language Bool) ∈ PvsNP.P := by
  have hset : ({x : List Bool | ∃ a b c : ℕ, x = List.replicate a false ++ List.replicate b true ++ List.replicate c false} : Language Bool)
      = {x : List Bool | F (x.foldl δ St.s0) = true} := by
    ext x
    exact (correct x).1.symm
  rw [hset]
  exact PvsNP.Units.m2_dfa_in_p St δ St.s0 F
