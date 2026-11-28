import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m3_models_count_disjoint_product

namespace PvsNP.Units.m3_y_shift_disjoint_sat

open PvsNP.Units.m3_models_count_disjoint_product

private def unshift (a : assgn) (k : ℕ) : assgn :=
  (a.filter (fun v => decide (k ≤ v))).map (fun v => v - k)

private theorem mem_unshift (a : assgn) (k v : ℕ) :
    v ∈ unshift a k ↔ v + k ∈ a := by
  simp only [unshift, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨n, ⟨hn, hkn⟩, h⟩
    have eqn : n = v + k := by omega
    simpa only [eqn] using hn
  · intro hv
    exact ⟨v + k, ⟨hv, by omega⟩, by omega⟩

private def combine (a b : assgn) (k : ℕ) : assgn :=
  a.filter (fun v => decide (v < k)) ++ b.map (fun v => v + k)

private theorem source_mem (a b : assgn) (k v : ℕ) (lt : v < k) :
    v ∈ combine a b k ↔ v ∈ a := by
  simp only [combine, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_map]
  constructor
  · rintro (⟨h, _⟩ | ⟨w, _, hw⟩)
    · exact h
    · omega
  · intro h
    exact Or.inl ⟨h, lt⟩

private theorem shifted_mem (a b : assgn) (k v : ℕ) :
    v + k ∈ combine a b k ↔ v ∈ b := by
  simp only [combine, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_map]
  constructor
  · rintro (⟨_, h⟩ | ⟨w, hw, he⟩)
    · omega
    · exact Nat.add_right_cancel he ▸ hw
  · intro hv
    exact Or.inr ⟨v, hv, rfl⟩

end PvsNP.Units.m3_y_shift_disjoint_sat

open PvsNP.Units.m3_y_shift_disjoint_sat PvsNP.Units.m3_models_count_disjoint_product in
theorem PvsNP.Units.m3_y_shift_disjoint_sat :
    ∀ (N M : cnf) (k : ℕ), (∀ C ∈ N, ∀ l ∈ C, l.2 < k) →
      (SAT (N ++ M.map (fun C => C.map (fun l => (l.1, l.2 + k)))) ↔ SAT N ∧ SAT M) := by
  intro N M k bound
  constructor
  · rintro ⟨a, ha⟩
    change (N ++ _).all (evalClause a) = true at ha
    rw [List.all_append, Bool.and_eq_true] at ha
    refine ⟨⟨a, ha.1⟩, ⟨unshift a k, ?_⟩⟩
    change evalCnf (unshift a k) M = true
    rw [← evalCnf_shift a M k (unshift a k) (fun _ _ l _ => (mem_unshift a k l.2).symm)]
    exact ha.2
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    let c := combine a b k
    refine ⟨c, ?_⟩
    have hN := evalCnf_congr c a N (fun C hc l hl => source_mem a b k l.2 (bound C hc l hl))
    have hM := evalCnf_shift c M k b (fun _ _ l _ => shifted_mem a b k l.2)
    change (N ++ _).all (evalClause c) = true
    rw [List.all_append, Bool.and_eq_true]
    exact ⟨hN.trans ha, hM.trans hb⟩
