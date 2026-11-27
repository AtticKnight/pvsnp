import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_dfa_in_p

/-- The strings whose length is 1 modulo 3 are in P: a one-pass finite
    automaton with states `Fin 3` (the running length mod 3), decided by the
    settled unit `m2_dfa_in_p`. -/
theorem PvsNP.Units.tl_lang_len_mod_p :
    ({x : List Bool | x.length % 3 = 1} : Language Bool) ∈ PvsNP.P := by
  have key : ∀ (x : List Bool) (q : Fin 3),
      (x.foldl (fun q _ => q + 1) q).val
        = (q.val + x.length) % 3 := by
    intro x
    induction x with
    | nil =>
      intro q
      simp [Nat.mod_eq_of_lt q.isLt]
    | cons b x ih =>
      intro q
      show (x.foldl (fun q _ => q + 1) (q + 1)).val
        = (q.val + (b :: x).length) % 3
      rw [ih (q + 1)]
      have h1 : (q + 1 : Fin 3).val = (q.val + 1) % 3 := by
        rw [Fin.val_add, Fin.val_one]
      rw [h1]
      simp only [List.length_cons]
      omega
  have hset : ({x : List Bool | x.length % 3 = 1} : Language Bool)
      = {x : List Bool | (fun q : Fin 3 => decide (q = 1))
          (x.foldl (fun q _ => q + 1) 0) = true} := by
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
  exact PvsNP.Units.m2_dfa_in_p (Fin 3) (fun q _ => q + 1) 0
    (fun q => decide (q = 1))
