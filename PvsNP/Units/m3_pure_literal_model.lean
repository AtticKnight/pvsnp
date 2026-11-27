import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_pure_literal_model :
    ∀ (N : cnf) (l : literal), (∀ C ∈ N, (!l.1, l.2) ∉ C) → SAT N →
      ∃ a : assgn, satisfiesCnf a N ∧ evalLiteral a l = true := by
  intro N l hpure hsat
  rcases l with ⟨pol, v⟩
  rcases hsat with ⟨a, ha⟩
  let a' : assgn := if pol then v :: a else a.filter (fun u => decide (u ≠ v))
  have hav : evalVar a' v = pol := by
    cases pol
    · simp [a', evalVar, List.mem_filter]
    · simp [a', evalVar]
  have ha_ne : ∀ u : var, u ≠ v → evalVar a' u = evalVar a u := by
    intro u hu
    cases pol
    · simp [a', evalVar, List.mem_filter, hu]
    · simp [a', evalVar, hu]
  refine ⟨a', (evalCnf_clause_iff a' N).mpr ?_, by simp [evalLiteral, hav]⟩
  intro C hC
  by_cases hlC : (pol, v) ∈ C
  · exact (evalClause_literal_iff a' C).mpr ⟨(pol, v), hlC, by simp [evalLiteral, hav]⟩
  · have hCa : evalClause a C = true := (evalCnf_clause_iff a N).mp ha C hC
    obtain ⟨m, hmC, hma⟩ := (evalClause_literal_iff a C).mp hCa
    refine (evalClause_literal_iff a' C).mpr ⟨m, hmC, ?_⟩
    rcases m with ⟨mp, mv⟩
    have hmv : mv ≠ v := by
      intro heq
      subst heq
      by_cases hmp : mp = pol
      · subst hmp; exact hlC hmC
      · have : mp = !pol := by cases mp <;> cases pol <;> simp_all
        subst this
        exact hpure C hC hmC
    simp only [evalLiteral] at hma ⊢
    rw [ha_ne mv hmv]
    exact hma
