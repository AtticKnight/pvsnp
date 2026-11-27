import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_y_xor_path_alternating

def xorPath (n : ℕ) : cnf :=
  (List.range n).flatMap (fun i => [[(true, i), (true, i + 1)], [(false, i), (false, i + 1)]])

theorem evalClause_pos (a : assgn) (i j : var) :
    evalClause a [(true, i), (true, j)] = true ↔ i ∈ a ∨ j ∈ a := by
  simp [evalClause, evalLiteral, evalVar]

theorem evalClause_neg (a : assgn) (i j : var) :
    evalClause a [(false, i), (false, j)] = true ↔ i ∉ a ∨ j ∉ a := by
  simp [evalClause, evalLiteral, evalVar]

theorem satisfies_xorPath_iff (n : ℕ) (a : assgn) :
    satisfiesCnf a (xorPath n) ↔ ∀ i < n, (i ∈ a ↔ i + 1 ∉ a) := by
  simp only [xorPath, satisfiesCnf, evalCnf, List.all_eq_true, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro h i hi
    have h1 := (evalClause_pos a i (i + 1)).1 (h _ ⟨i, hi, Or.inl rfl⟩)
    have h2 := (evalClause_neg a i (i + 1)).1 (h _ ⟨i, hi, Or.inr rfl⟩)
    by_cases ha : i ∈ a <;> by_cases hb : i + 1 ∈ a <;> simp [ha, hb] at h1 h2 ⊢
  · rintro h C ⟨i, hi, rfl | rfl⟩
    · rw [evalClause_pos]
      have := h i hi
      by_cases ha : i ∈ a <;> by_cases hb : i + 1 ∈ a <;> simp [ha, hb] at this ⊢
    · rw [evalClause_neg]
      have := h i hi
      by_cases ha : i ∈ a <;> by_cases hb : i + 1 ∈ a <;> simp [ha, hb] at this ⊢

theorem alternating_aux (n : ℕ) (a : assgn) :
    satisfiesCnf a (xorPath n) ↔ ∀ i ≤ n, (i ∈ a ↔ (0 ∈ a ↔ i % 2 = 0)) := by
  rw [satisfies_xorPath_iff]
  constructor
  · intro h i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hstep := h i (by omega)
      have hprev := ih (by omega)
      have hpar : (i + 1) % 2 = 0 ↔ ¬ (i % 2 = 0) := by omega
      tauto
  · intro h i hi
    have h1 := h i (by omega)
    have h2 := h (i + 1) (by omega)
    have hpar : (i + 1) % 2 = 0 ↔ ¬ (i % 2 = 0) := by omega
    tauto

end PvsNP.Units.m3_y_xor_path_alternating

/-- An assignment satisfies an XOR path iff its truth values alternate along 0..n. -/
theorem PvsNP.Units.m3_y_xor_path_alternating :
    ∀ (n : ℕ) (a : assgn),
      satisfiesCnf a ((List.range n).flatMap (fun i =>
        [[(true, i), (true, i + 1)], [(false, i), (false, i + 1)]])) ↔
        ∀ i ≤ n, (i ∈ a ↔ (0 ∈ a ↔ i % 2 = 0)) :=
  PvsNP.Units.m3_y_xor_path_alternating.alternating_aux
