import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_y_implication_cycle_equal

theorem evalClause_imp (a : assgn) (i j : var) :
    evalClause a [(false, i), (true, j)] = true ↔ (i ∈ a → j ∈ a) := by
  simp only [evalClause, evalLiteral, evalVar, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_true, decide_eq_false_iff_not, decide_eq_true_eq]
  tauto

theorem imp_cycle_step_iff (n : ℕ) (a : assgn) :
    satisfiesCnf a ((List.range n).map (fun i => [(false, i), (true, (i + 1) % n)])) ↔
      ∀ i < n, i ∈ a → (i + 1) % n ∈ a := by
  simp only [satisfiesCnf, evalCnf, List.all_eq_true, List.mem_map, List.mem_range]
  constructor
  · intro h i hi
    exact (evalClause_imp a i ((i + 1) % n)).1 (h _ ⟨i, hi, rfl⟩)
  · rintro h C ⟨i, hi, rfl⟩
    exact (evalClause_imp a i ((i + 1) % n)).2 (h i hi)

theorem imp_cycle_walk {n : ℕ} (hn : 0 < n) {a : assgn}
    (hstep : ∀ i < n, i ∈ a → (i + 1) % n ∈ a) (k : ℕ) :
    ∀ j < n, j ∈ a → (j + k) % n ∈ a := by
  induction k with
  | zero =>
    intro j hj hja
    simpa [Nat.mod_eq_of_lt hj] using hja
  | succ k ih =>
    intro j hj hja
    have hk := ih j hj hja
    have hnext := hstep ((j + k) % n) (Nat.mod_lt _ hn) hk
    have hmod : ((j + k) % n + 1) % n = (j + (k + 1)) % n := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
    rw [hmod] at hnext
    exact hnext

theorem imp_cycle_equal_aux (n : ℕ) (a : assgn) :
    satisfiesCnf a ((List.range n).map (fun i => [(false, i), (true, (i + 1) % n)])) ↔
      ∀ i < n, (i ∈ a ↔ 0 ∈ a) := by
  rw [imp_cycle_step_iff]
  constructor
  · intro hstep i hi
    have hn : 0 < n := by omega
    constructor
    · intro hia
      have hw := imp_cycle_walk hn hstep (n - i) i hi hia
      have heq : (i + (n - i)) % n = 0 := by
        have : i + (n - i) = n := by omega
        rw [this, Nat.mod_self]
      rw [heq] at hw
      exact hw
    · intro h0a
      have hw := imp_cycle_walk hn hstep i 0 hn h0a
      simpa [Nat.mod_eq_of_lt hi] using hw
  · intro heq i hi hia
    have hn : 0 < n := by omega
    exact (heq ((i + 1) % n) (Nat.mod_lt _ hn)).2 ((heq i hi).1 hia)

end PvsNP.Units.m3_y_implication_cycle_equal

/-- An assignment satisfies an implication cycle on 0..n-1 iff all variables in 0..n-1 have the same value. -/
theorem PvsNP.Units.m3_y_implication_cycle_equal :
    ∀ (n : ℕ) (a : assgn),
      satisfiesCnf a ((List.range n).map (fun i => [(false, i), (true, (i + 1) % n)])) ↔
        ∀ i < n, (i ∈ a ↔ 0 ∈ a) :=
  PvsNP.Units.m3_y_implication_cycle_equal.imp_cycle_equal_aux
