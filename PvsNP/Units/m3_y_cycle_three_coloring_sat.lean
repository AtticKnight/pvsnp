import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_cycle_three_coloring_sat

private def col (n i : ℕ) : ℕ :=
  if i + 1 = n then 2 else i % 2

private lemma col_lt_three (n i : ℕ) : col n i < 3 := by
  unfold col
  split_ifs <;> omega

private lemma col_adj_ne {n i : ℕ} (hn : 2 ≤ n) (hi : i < n) :
    col n i ≠ col n ((i + 1) % n) := by
  unfold col
  by_cases h1 : i + 1 = n
  · have hmod : (i + 1) % n = 0 := by rw [h1, Nat.mod_self]
    rw [hmod]
    have h0 : ¬ (0 + 1 = n) := by omega
    simp [h1, h0]
  · have hlt : i + 1 < n := by omega
    have hmod : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt hlt
    rw [hmod]
    by_cases h2 : i + 1 + 1 = n
    · simp only [h1, ↓reduceIte, h2]
      omega
    · simp only [h1, ↓reduceIte, h2]
      omega

private lemma mem_asgn_iff (n v c : ℕ) (hv : v < n) (hc : c < 3) :
    v * 3 + c ∈ (List.range n).map (fun i => i * 3 + col n i) ↔ c = col n v := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, _, hi⟩
    have hci : col n i < 3 := col_lt_three n i
    have hiv : i = v := by omega
    subst hiv
    omega
  · rintro rfl
    exact ⟨v, hv, rfl⟩

end PvsNP.Units.m3_y_cycle_three_coloring_sat

/-- The 3-colouring clauses of the cycle on `n ≥ 2` vertices are satisfiable (vendored model). -/
theorem PvsNP.Units.m3_y_cycle_three_coloring_sat :
    ∀ n : ℕ, 2 ≤ n →
      SAT ((List.range n).map (fun v => (List.range 3).map (fun c => (true, v * 3 + c))) ++
        (List.range n).flatMap (fun i => (List.range 3).map
          (fun c => [(false, i * 3 + c), (false, ((i + 1) % n) * 3 + c)]))) := by
  intro n hn
  let a : assgn := (List.range n).map (fun i => i * 3 + PvsNP.Units.m3_y_cycle_three_coloring_sat.col n i)
  refine ⟨a, ?_⟩
  rw [satisfiesCnf, evalCnf_app_iff]
  constructor
  · rw [evalCnf_clause_iff]
    intro C hC
    rw [List.mem_map] at hC
    obtain ⟨v, hv_mem, rfl⟩ := hC
    have hv : v < n := List.mem_range.mp hv_mem
    rw [evalClause_literal_iff]
    refine ⟨(true, v * 3 + PvsNP.Units.m3_y_cycle_three_coloring_sat.col n v), ?_, ?_⟩
    · rw [List.mem_map]
      exact ⟨PvsNP.Units.m3_y_cycle_three_coloring_sat.col n v,
        List.mem_range.mpr (PvsNP.Units.m3_y_cycle_three_coloring_sat.col_lt_three n v), rfl⟩
    · have hmem : v * 3 + PvsNP.Units.m3_y_cycle_three_coloring_sat.col n v ∈ a :=
        (PvsNP.Units.m3_y_cycle_three_coloring_sat.mem_asgn_iff n v _ hv
          (PvsNP.Units.m3_y_cycle_three_coloring_sat.col_lt_three n v)).mpr rfl
      simp [evalLiteral, evalVar, hmem]
  · rw [evalCnf_clause_iff]
    intro C hC
    rw [List.mem_flatMap] at hC
    obtain ⟨i, hi_mem, hC_map⟩ := hC
    have hi : i < n := List.mem_range.mp hi_mem
    rw [List.mem_map] at hC_map
    obtain ⟨c, hc_mem, rfl⟩ := hC_map
    have hc : c < 3 := List.mem_range.mp hc_mem
    have hne := PvsNP.Units.m3_y_cycle_three_coloring_sat.col_adj_ne hn hi
    have hmod_lt : (i + 1) % n < n := Nat.mod_lt _ (by omega)
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
      evalLiteral, evalVar]
    by_cases hci : c = PvsNP.Units.m3_y_cycle_three_coloring_sat.col n i
    · right
      have hnc : c ≠ PvsNP.Units.m3_y_cycle_three_coloring_sat.col n ((i + 1) % n) := by
        rw [hci]; exact hne
      have hnot : ((i + 1) % n) * 3 + c ∉ a := fun h =>
        hnc ((PvsNP.Units.m3_y_cycle_three_coloring_sat.mem_asgn_iff n ((i + 1) % n) c hmod_lt hc).mp h)
      simp [hnot]
    · left
      have hnot : i * 3 + c ∉ a := fun h =>
        hci ((PvsNP.Units.m3_y_cycle_three_coloring_sat.mem_asgn_iff n i c hi hc).mp h)
      simp [hnot]
