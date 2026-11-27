import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_y_pad_cnf_fresh_var

private theorem expand_preserves_eval (a : assgn) (z : var) (N : cnf) :
    evalCnf a (N.flatMap (fun C => [C ++ [(true, z)], C ++ [(false, z)]])) = evalCnf a N := by
  induction N with
  | nil => rfl
  | cons C N ih =>
    change (evalClause a (C ++ [(true, z)]) && (evalClause a (C ++ [(false, z)]) &&
      evalCnf a (N.flatMap (fun D => [D ++ [(true, z)], D ++ [(false, z)]])))) =
        (evalClause a C && evalCnf a N)
    rw [ih]
    cases hc : evalClause a C <;> cases hv : evalVar a z <;>
      simp only [evalClause] at hc <;> simp [evalClause, List.any_append, evalLiteral, hc, hv]

end PvsNP.Units.m3_y_pad_cnf_fresh_var

theorem PvsNP.Units.m3_y_pad_cnf_fresh_var :
    ∀ (N : cnf) (k : ℕ) (z : var), (∀ C ∈ N, C.length ≤ k) →
      (∀ C ∈ N.flatMap (fun C => [C ++ [(true, z)], C ++ [(false, z)]]), C.length ≤ k + 1) ∧
      (SAT (N.flatMap (fun C => [C ++ [(true, z)], C ++ [(false, z)]])) ↔ SAT N) := by
  intro N k z hk
  constructor
  · intro D hD
    obtain ⟨C, hC, hD⟩ := List.mem_flatMap.mp hD
    have bound := hk C hC
    rcases (List.mem_cons.mp hD) with rfl | hlast
    · simpa using Nat.add_le_add_right bound 1
    · obtain rfl := List.mem_singleton.mp hlast
      simpa using Nat.add_le_add_right bound 1
  · constructor <;> rintro ⟨a, ha⟩ <;> refine ⟨a, ?_⟩ <;>
      simpa only [satisfiesCnf, PvsNP.Units.m3_y_pad_cnf_fresh_var.expand_preserves_eval] using ha
