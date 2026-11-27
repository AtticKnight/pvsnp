import Mathlib
import PvsNP.Defs
import CookLevin

/-- The empty assignment satisfies a CNF of negative literals exactly when it has no empty clause. -/
theorem PvsNP.Units.m3_negative_cnf_empty_model :
    ∀ N : cnf, (∀ C ∈ N, ∀ l ∈ C, l.1 = false) → (satisfiesCnf [] N ↔ [] ∉ N) := by
  intro N hneg
  simp only [satisfiesCnf, evalCnf, List.all_eq_true]
  constructor
  · intro h hnil
    have h1 := h [] hnil
    simp [evalClause] at h1
  · intro hne C hC
    have hCne : C ≠ [] := fun hc => hne (hc ▸ hC)
    obtain ⟨⟨s, v⟩, hl⟩ := List.exists_mem_of_ne_nil C hCne
    have hs : s = false := hneg C hC (s, v) hl
    subst hs
    simp only [evalClause, List.any_eq_true]
    exact ⟨(false, v), hl, by simp [evalLiteral, evalVar]⟩
