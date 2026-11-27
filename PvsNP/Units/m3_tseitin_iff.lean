import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_tseitin_iff :
    ∀ (N : cnf) (z : var) (l₁ l₂ : literal), l₁.2 ≠ z → l₂.2 ≠ z → (∀ C ∈ N, ∀ l ∈ C, l.2 ≠ z) →
      (SAT ([(false, z), (!l₁.1, l₁.2), l₂] :: [(false, z), l₁, (!l₂.1, l₂.2)] ::
          [(true, z), l₁, l₂] :: [(true, z), (!l₁.1, l₁.2), (!l₂.1, l₂.2)] :: N) ↔ SAT N) := by
  intro N z l₁ l₂ h1 h2 hN
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, (evalCnf_clause_iff a N).mpr (fun C hC => ?_)⟩
    exact (evalCnf_clause_iff a _).mp ha C
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))
  · rintro ⟨a, ha⟩
    set val : Bool := evalLiteral a l₁ == evalLiteral a l₂
    let a' : assgn := if val then z :: a else a.filter (fun u => decide (u ≠ z))
    have haz : evalVar a' z = val := by cases h : val <;> simp [a', h, evalVar, List.mem_filter]
    have ha_ne : ∀ u : var, u ≠ z → evalVar a' u = evalVar a u := by
      intro u hu; cases h : val <;> simp [a', h, evalVar, List.mem_filter, hu]
    refine ⟨a', (evalCnf_clause_iff a' _).mpr ?_⟩
    intro C hC
    rcases l₁ with ⟨s₁, v₁⟩
    rcases l₂ with ⟨s₂, v₂⟩
    rcases List.mem_cons.mp hC with rfl | hC
    · simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false,
        haz, ha_ne v₁ h1, ha_ne v₂ h2, val]
      cases evalVar a v₁ <;> cases s₁ <;> cases evalVar a v₂ <;> cases s₂ <;> rfl
    · rcases List.mem_cons.mp hC with rfl | hC
      · simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false,
          haz, ha_ne v₁ h1, ha_ne v₂ h2, val]
        cases evalVar a v₁ <;> cases s₁ <;> cases evalVar a v₂ <;> cases s₂ <;> rfl
      · rcases List.mem_cons.mp hC with rfl | hC
        · simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false,
            haz, ha_ne v₁ h1, ha_ne v₂ h2, val]
          cases evalVar a v₁ <;> cases s₁ <;> cases evalVar a v₂ <;> cases s₂ <;> rfl
        · rcases List.mem_cons.mp hC with rfl | hC
          · simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false,
              haz, ha_ne v₁ h1, ha_ne v₂ h2, val]
            cases evalVar a v₁ <;> cases s₁ <;> cases evalVar a v₂ <;> cases s₂ <;> rfl
          · obtain ⟨m, hm, hma⟩ := (evalClause_literal_iff a C).mp ((evalCnf_clause_iff a N).mp ha C hC)
            refine (evalClause_literal_iff a' C).mpr ⟨m, hm, ?_⟩
            simp only [evalLiteral] at hma ⊢
            rw [ha_ne m.2 (hN C hC m hm)]
            exact hma
