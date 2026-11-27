import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

/-- The strings whose number of trues is 0 modulo 3 are in P: a one-pass finite
    automaton with states `Fin 3` (the running count mod 3), decided by the
    settled unit `m2_dfa_in_p`. -/
theorem PvsNP.Units.tl_lang_count_mod_p :
    ({x : List Bool | x.count true % 3 = 0} : Language Bool) ∈ PvsNP.P := by
  have key : ∀ (x : List Bool) (q : Fin 3),
      (x.foldl (fun q b => if b then q + 1 else q) q).val
        = (q.val + x.count true) % 3 := by
    intro x
    induction x with
    | nil =>
      intro q
      simp [Nat.mod_eq_of_lt q.isLt]
    | cons b x ih =>
      intro q
      cases b with
      | false =>
        show (x.foldl (fun q b => if b then q + 1 else q) q).val
          = (q.val + (false :: x).count true) % 3
        rw [ih q]
        simp
      | true =>
        show (x.foldl (fun q b => if b then q + 1 else q) (q + 1)).val
          = (q.val + (true :: x).count true) % 3
        rw [ih (q + 1)]
        have h1 : (q + 1 : Fin 3).val = (q.val + 1) % 3 := by
          rw [Fin.val_add, Fin.val_one]
        rw [h1]
        have h2 : (true :: x).count true = x.count true + 1 := by simp
        rw [h2]
        omega
  have hset : ({x : List Bool | x.count true % 3 = 0} : Language Bool)
      = {x : List Bool | (fun q : Fin 3 => decide (q = 0))
          (x.foldl (fun q b => if b then q + 1 else q) 0) = true} := by
    ext x
    simp only [Set.mem_setOf_eq, decide_eq_true_eq]
    have h0 := key x 0
    simp only [Fin.val_zero, Nat.zero_add] at h0
    constructor
    · intro h
      apply Fin.ext
      rw [h0, h]
      rfl
    · intro h
      rw [← h0]
      exact congrArg Fin.val h
  rw [hset]
  exact PvsNP.Units.m2_dfa_in_p (Fin 3) (fun q b => if b then q + 1 else q) 0
    (fun q => decide (q = 0))
