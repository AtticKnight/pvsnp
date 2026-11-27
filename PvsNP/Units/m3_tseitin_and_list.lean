import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_tseitin_and_list

theorem same {z : var} {a a' : assgn} (h : ∀ x, x ≠ z → (x ∈ a' ↔ x ∈ a)) (l : literal)
    (hl : l.2 ≠ z) : evalLiteral a' l = evalLiteral a l := by
  rcases l with ⟨s, x⟩
  have hx := h x hl
  by_cases m : x ∈ a
  · have m' := hx.mpr m
    simp [evalLiteral, evalVar, m, m']
  · have m' : x ∉ a' := fun c => m (hx.mp c)
    simp [evalLiteral, evalVar, m, m']

theorem lit (a : assgn) (l : literal) : evalLiteral a (!l.1, l.2) = !evalLiteral a l := by
  rcases l with ⟨s, v⟩
  simp only [evalLiteral]
  cases evalVar a v <;> cases s <;> rfl

end PvsNP.Units.m3_tseitin_and_list

open PvsNP.Units.m3_tseitin_and_list in
theorem PvsNP.Units.m3_tseitin_and_list : ∀ (N : cnf) (z : var) (ls : List literal), (∀ l ∈ ls, l.2 ≠ z) → (∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z) →
  (SAT ((((true, z) :: ls.map (fun l => (!l.1, l.2))) :: ls.map (fun l => [(false, z), l])) ++ N) ↔ SAT N) := by
  intro N z ls hls hN
  constructor
  · rintro ⟨a, ha⟩
    have ha' := (evalCnf_clause_iff a _).mp ha
    refine ⟨a, ?_⟩
    apply (evalCnf_clause_iff a N).mpr
    intro C hC
    exact ha' C (List.mem_append_right _ hC)
  · rintro ⟨a, ha⟩
    have ha' := (evalCnf_clause_iff a N).mp ha
    have keep : ∀ a' : assgn, (∀ x, x ≠ z → (x ∈ a' ↔ x ∈ a)) → ∀ C ∈ N, evalClause a' C = true := by
      intro a' hs C hC
      obtain ⟨l, hl, ht⟩ := (evalClause_literal_iff a C).mp (ha' C hC)
      exact (evalClause_literal_iff _ _).mpr ⟨l, hl, (same hs l (hN C hC l hl)).trans ht⟩
    by_cases hall : ∀ l ∈ ls, evalLiteral a l = true
    · refine ⟨z :: a, ?_⟩
      have hs : ∀ x, x ≠ z → (x ∈ z :: a ↔ x ∈ a) := by
        intro x hx
        simp [hx]
      apply (evalCnf_clause_iff _ _).mpr
      intro C hC
      rcases List.mem_append.mp hC with h1 | h1
      · rcases List.mem_cons.mp h1 with rfl | h2
        · exact (evalClause_literal_iff _ _).mpr
            ⟨(true, z), List.mem_cons_self, by simp [evalLiteral, evalVar]⟩
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp h2
          exact (evalClause_literal_iff _ _).mpr
            ⟨l, by simp, (same hs l (hls l hl)).trans (hall l hl)⟩
      · exact keep _ hs C h1
    · obtain ⟨l0, hl0'⟩ := not_forall.mp hall
      obtain ⟨hl0, hf0⟩ := Classical.not_imp.mp hl0'
      refine ⟨a.filter (fun x => decide (x ≠ z)), ?_⟩
      have hs : ∀ x, x ≠ z → (x ∈ a.filter (fun x => decide (x ≠ z)) ↔ x ∈ a) := by
        intro x hx
        simp [hx]
      have hzn : z ∉ a.filter (fun x => decide (x ≠ z)) := by simp
      apply (evalCnf_clause_iff _ _).mpr
      intro C hC
      rcases List.mem_append.mp hC with h1 | h1
      · rcases List.mem_cons.mp h1 with rfl | h2
        · refine (evalClause_literal_iff _ _).mpr ⟨(!l0.1, l0.2), ?_, ?_⟩
          · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨l0, hl0, rfl⟩)
          · have hz0 : ((!l0.1, l0.2) : literal).2 ≠ z := hls l0 hl0
            rw [same hs _ hz0, lit]
            cases h : evalLiteral a l0
            · rfl
            · exact absurd h hf0
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp h2
          exact (evalClause_literal_iff _ _).mpr
            ⟨(false, z), by simp, by simp [evalLiteral, evalVar, hzn]⟩
      · exact keep _ hs C h1
