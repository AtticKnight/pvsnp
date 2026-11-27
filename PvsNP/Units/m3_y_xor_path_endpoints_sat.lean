import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_y_xor_path_endpoints_sat

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

theorem alternating_iff (n : ℕ) (a : assgn) :
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

theorem endpoints_sat_aux (n : ℕ) :
    SAT ([(true, 0)] :: [(true, n)] :: xorPath n) ↔ n % 2 = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha
    obtain ⟨h0, hn, hpath⟩ := ha
    have h0m : 0 ∈ a := by simpa [evalClause, evalLiteral, evalVar] using h0
    have hnm : n ∈ a := by simpa [evalClause, evalLiteral, evalVar] using hn
    have halt := (alternating_iff n a).1 hpath n (le_refl n)
    exact (halt.1 hnm).1 h0m
  · intro hn
    let a : assgn := (List.range (n + 1)).filter (fun i => decide (i % 2 = 0))
    refine ⟨a, ?_⟩
    simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true]
    have h0m : 0 ∈ a := by simp [a]
    have hnm : n ∈ a := by simp [a, hn]
    have h0 : evalClause a [(true, 0)] = true := by simp [evalClause, evalLiteral, evalVar, h0m]
    have h1 : evalClause a [(true, n)] = true := by simp [evalClause, evalLiteral, evalVar, hnm]
    have hpath : satisfiesCnf a (xorPath n) := by
      rw [alternating_iff]
      intro i hi
      have hilt : i < n + 1 := by omega
      simp [a, h0m, hilt]
    exact ⟨h0, h1, hpath⟩

end PvsNP.Units.m3_y_xor_path_endpoints_sat

/-- An XOR path with both endpoints forced true is satisfiable iff n is even. -/
theorem PvsNP.Units.m3_y_xor_path_endpoints_sat :
    ∀ n : ℕ,
      SAT ([(true, 0)] :: [(true, n)] ::
        (List.range n).flatMap (fun i =>
          [[(true, i), (true, i + 1)], [(false, i), (false, i + 1)]])) ↔
        n % 2 = 0 :=
  PvsNP.Units.m3_y_xor_path_endpoints_sat.endpoints_sat_aux
