import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_pure_literal :
    ∀ (N : cnf) (l : literal), (∀ C ∈ N, (!l.1, l.2) ∉ C) →
      (SAT N ↔ SAT (N.filter (fun C => decide (l ∉ C)))) := by
  intro N l hpure
  rcases l with ⟨pol, v⟩
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, (evalCnf_clause_iff a _).mpr ?_⟩
    intro C hC
    rw [List.mem_filter] at hC
    exact (evalCnf_clause_iff a N).mp ha C hC.1
  · rintro ⟨a, ha⟩
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
    refine ⟨a', (evalCnf_clause_iff a' N).mpr ?_⟩
    intro C hC
    by_cases hlC : (pol, v) ∈ C
    · exact (evalClause_literal_iff a' C).mpr ⟨(pol, v), hlC, by simp [evalLiteral, hav]⟩
    · have hCf : C ∈ N.filter (fun C => decide ((pol, v) ∉ C)) :=
        List.mem_filter.mpr ⟨hC, decide_eq_true hlC⟩
      have hCa : evalClause a C = true := (evalCnf_clause_iff a _).mp ha C hCf
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
