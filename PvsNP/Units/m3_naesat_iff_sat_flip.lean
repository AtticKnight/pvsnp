import Mathlib
import PvsNP.Defs
import CookLevin

/-!
# Unit `m3_naesat_iff_sat_flip`

Not-all-equal satisfiability of `N` is satisfiability of `N` together with
its sign-flipped copy: flipping a literal's sign negates its value, so a
flipped clause is true exactly when the original clause has a false
literal. The same assignment works both ways.
-/

namespace PvsNP.Units.m3_naesat_iff_sat_flip

theorem evalLiteral_flip (a : assgn) (l : literal) :
    evalLiteral a (!l.1, l.2) = !evalLiteral a l := by
  obtain ⟨s, v⟩ := l
  cases h : evalVar a v <;> cases s <;> simp [evalLiteral, h]

theorem any_flip (a : assgn) (C : List literal) :
    (C.map (fun l => (!l.1, l.2))).any (evalLiteral a) =
      C.any (fun l => !evalLiteral a l) := by
  induction C with
  | nil => rfl
  | cons l C ih => simp [evalLiteral_flip a l, ih]

theorem evalClause_eq_any (a : assgn) (C : List literal) :
    evalClause a C = true ↔ C.any (evalLiteral a) = true := by
  rw [evalClause_literal_iff, List.any_eq_true]

end PvsNP.Units.m3_naesat_iff_sat_flip

theorem PvsNP.Units.m3_naesat_iff_sat_flip :
    ∀ N : cnf,
      (∃ a : assgn, ∀ C ∈ N, C.any (evalLiteral a) = true ∧
        C.any (fun l => !evalLiteral a l) = true) ↔
        SAT (N ++ N.map (fun C => C.map (fun l => (!l.1, l.2)))) := by
  intro N
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    show evalCnf a (N ++ N.map (fun C => C.map (fun l => (!l.1, l.2)))) = true
    rw [evalCnf_clause_iff]
    intro C hC
    rw [List.mem_append] at hC
    rcases hC with hC | hC
    · exact (PvsNP.Units.m3_naesat_iff_sat_flip.evalClause_eq_any a C).mpr
        (ha C hC).1
    · rw [List.mem_map] at hC
      obtain ⟨C₀, hC₀, rfl⟩ := hC
      refine (PvsNP.Units.m3_naesat_iff_sat_flip.evalClause_eq_any a _).mpr ?_
      rw [PvsNP.Units.m3_naesat_iff_sat_flip.any_flip]
      exact (ha C₀ hC₀).2
  · rintro ⟨a, ha⟩
    have ha' : evalCnf a
        (N ++ N.map (fun C => C.map (fun l => (!l.1, l.2)))) = true := ha
    rw [evalCnf_clause_iff] at ha'
    refine ⟨a, ?_⟩
    intro C hC
    constructor
    · exact (PvsNP.Units.m3_naesat_iff_sat_flip.evalClause_eq_any a C).mp
        (ha' C (List.mem_append_left _ hC))
    · rw [← PvsNP.Units.m3_naesat_iff_sat_flip.any_flip a C]
      exact (PvsNP.Units.m3_naesat_iff_sat_flip.evalClause_eq_any a _).mp
        (ha' _ (List.mem_append_right _
          (List.mem_map.mpr ⟨C, hC, rfl⟩)))
