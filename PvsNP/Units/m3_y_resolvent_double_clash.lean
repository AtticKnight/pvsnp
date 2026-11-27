import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_y_resolvent_double_clash :
    ∀ (C D : clause) (v w : var) (a : assgn), v ≠ w →
      (true, v) ∈ C → (false, v) ∈ D → (true, w) ∈ C → (false, w) ∈ D →
      evalClause a (C.filter (fun l => decide (l ≠ (true, v))) ++
        D.filter (fun l => decide (l ≠ (false, v)))) = true := by
  intro C D v w a hvw _ _ hpos hneg
  rw [evalClause_literal_iff]
  by_cases hw : evalVar a w = true
  · refine ⟨(true, w), List.mem_append.mpr (Or.inl ?_), by simp [evalLiteral, hw]⟩
    exact List.mem_filter.mpr ⟨hpos, by simp [Ne.symm hvw]⟩
  · refine ⟨(false, w), List.mem_append.mpr (Or.inr ?_), by simp [evalLiteral, hw]⟩
    exact List.mem_filter.mpr ⟨hneg, by simp [Ne.symm hvw]⟩
