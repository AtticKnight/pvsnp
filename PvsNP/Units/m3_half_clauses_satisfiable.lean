import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_half_clauses_satisfiable

theorem cover_count (N : cnf) (P Q : clause → Bool)
    (h : ∀ C ∈ N, P C = true ∨ Q C = true) :
    N.length ≤ (N.filter P).length + (N.filter Q).length := by
  induction N with
  | nil => simp
  | cons C N ih =>
      have ih' := ih (fun D hD => h D (List.mem_cons_of_mem _ hD))
      rcases h C (List.mem_cons_self) with hp | hq
      · simp only [List.filter_cons, hp, if_true, List.length_cons]
        split <;> simp <;> omega
      · simp only [List.filter_cons, hq, if_true, List.length_cons]
        split <;> simp <;> omega

end PvsNP.Units.m3_half_clauses_satisfiable

open PvsNP.Units.m3_half_clauses_satisfiable in
theorem PvsNP.Units.m3_half_clauses_satisfiable :
    ∀ N : cnf, [] ∉ N → ∃ a : assgn, N.length ≤ 2 * (N.filter (evalClause a)).length := by
  intro N hN
  let A : assgn := N.flatten.map Prod.snd
  have hcov : ∀ C ∈ N, evalClause [] C = true ∨ evalClause A C = true := by
    intro C hC
    match C, hC with
    | [], hC => exact absurd hC hN
    | (s, v) :: rest, hC =>
      cases s with
      | false =>
          left
          simp [evalClause, evalLiteral, evalVar]
      | true =>
          right
          have hv : v ∈ A := by
            simp only [A, List.mem_map, List.mem_flatten]
            exact ⟨(true, v), ⟨_, hC, List.mem_cons_self⟩, rfl⟩
          simp [evalClause, evalLiteral, evalVar, hv]
  have hc := cover_count N (evalClause []) (evalClause A) hcov
  by_cases h1 : (N.filter (evalClause A)).length ≤ (N.filter (evalClause [])).length
  · exact ⟨[], by omega⟩
  · exact ⟨A, by omega⟩
