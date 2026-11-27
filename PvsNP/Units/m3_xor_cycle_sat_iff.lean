import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

open CookLevin

namespace PvsNP.Units.m3_xor_cycle_sat_iff

def cyc (n : ℕ) : cnf :=
  (List.range n).flatMap (fun i => [[(true, i), (true, (i + 1) % n)], [(false, i), (false, (i + 1) % n)]])

theorem sat_iff_xor (n : ℕ) (a : assgn) :
    satisfiesCnf a (cyc n) ↔ ∀ i < n, (i ∈ a ↔ ¬ ((i + 1) % n ∈ a)) := by
  unfold satisfiesCnf evalCnf cyc
  simp only [List.all_flatMap, List.all_eq_true, List.mem_range, evalClause, evalLiteral, evalVar,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil]
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  by_cases h1 : i ∈ a <;> by_cases h2 : (i + 1) % n ∈ a <;> simp [h1, h2]

theorem even_sat (n : ℕ) (h : n % 2 = 0) : SAT (cyc n) := by
  refine ⟨(List.range n).filter (fun i => i % 2 = 0), (sat_iff_xor n _).2 ?_⟩
  intro i hi
  have hn : 0 < n := by omega
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  by_cases hc : i + 1 < n
  · rw [Nat.mod_eq_of_lt hc]; rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;> simp [hp] <;> omega
  · have : i + 1 = n := by omega
    rw [this, Nat.mod_self]; rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;> simp [hp] <;> omega

theorem odd_unsat (n : ℕ) (h : n % 2 = 1) : ¬ SAT (cyc n) := by
  rintro ⟨a, ha⟩
  have key := (sat_iff_xor n a).1 ha
  have step : ∀ i, i < n → (i ∈ a ↔ ((0 ∈ a) ↔ i % 2 = 0)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := key k (by omega)
      rw [Nat.mod_eq_of_lt hk] at h1
      have := ih (by omega)
      rcases Nat.mod_two_eq_zero_or_one k with hp | hp
      · have hq : (k + 1) % 2 = 1 := by omega
        simp only [hp, hq] at this ⊢
        by_cases h0 : 0 ∈ a <;> simp [h0] at this ⊢ <;> tauto
      · have hq : (k + 1) % 2 = 0 := by omega
        simp only [hp, hq] at this ⊢
        by_cases h0 : 0 ∈ a <;> simp [h0] at this ⊢ <;> tauto
  have hl := key (n - 1) (by omega)
  have e : n - 1 + 1 = n := by omega
  rw [e, Nat.mod_self] at hl
  have := step (n - 1) (by omega)
  by_cases h0 : 0 ∈ a <;> simp_all <;> omega

end PvsNP.Units.m3_xor_cycle_sat_iff

theorem PvsNP.Units.m3_xor_cycle_sat_iff :
    ∀ n : ℕ,
      SAT ((List.range n).flatMap (fun i => [[(true, i), (true, (i + 1) % n)], [(false, i), (false, (i + 1) % n)]])) ↔
        n % 2 = 0 := by
  intro n
  show SAT (PvsNP.Units.m3_xor_cycle_sat_iff.cyc n) ↔ _
  refine ⟨fun h => ?_, PvsNP.Units.m3_xor_cycle_sat_iff.even_sat n⟩
  by_contra hn
  exact PvsNP.Units.m3_xor_cycle_sat_iff.odd_unsat n (by omega) h
