import Mathlib
import PvsNP.Defs
import CookLevin

/-
Original proof of `PvsNP.Units.m3_blocked_clause`: a clause `C` blocked on its literal `l` in `N`
can be added or removed without changing satisfiability. Adding it is the hard direction: given
an assignment `a` satisfying `N` but not `C`, set the variable of `l` so that `l` holds. A clause
`D` of `N` that loses its true literal by this change contains the complement of `l`, so by the
blocking condition it also contains the complement of some other literal `m` of `C`; that
complement is true under `a`, on a variable other than that of `l`, so `D` stays satisfied. The
flipped assignment follows the one in `PvsNP/Units/m3_pure_literal.lean` of this repository.
-/

theorem PvsNP.Units.m3_blocked_clause :
    ∀ (N : cnf) (C : clause) (l : literal), l ∈ C →
      (∀ D ∈ N, (!l.1, l.2) ∈ D → ∃ m ∈ C, m ≠ l ∧ (!m.1, m.2) ∈ D) →
        (SAT (C :: N) ↔ SAT N) := by
  intro N C l hlC hblk
  rcases l with ⟨pol, v⟩
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, (evalCnf_clause_iff a N).mpr ?_⟩
    intro D hD
    exact (evalCnf_clause_iff a _).mp ha D (List.mem_cons_of_mem _ hD)
  · rintro ⟨a, ha⟩
    have haN : ∀ D ∈ N, evalClause a D = true := (evalCnf_clause_iff a N).mp ha
    by_cases hCa : evalClause a C = true
    · refine ⟨a, (evalCnf_clause_iff a _).mpr ?_⟩
      intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact hCa
      · exact haN D hD
    · -- every literal of `C` is false under `a`
      have hCfalse : ∀ m ∈ C, evalLiteral a m = false := by
        intro m hm
        by_contra hne
        exact hCa ((evalClause_literal_iff a C).mpr ⟨m, hm, by simpa using hne⟩)
      have hav0 : evalVar a v = !pol := by
        have := hCfalse (pol, v) hlC
        simp only [evalLiteral, decide_eq_false_iff_not] at this
        cases h : evalVar a v <;> cases pol <;> simp_all
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
      refine ⟨a', (evalCnf_clause_iff a' _).mpr ?_⟩
      intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact (evalClause_literal_iff a' _).mpr ⟨(pol, v), hlC, by simp [evalLiteral, hav]⟩
      · obtain ⟨m0, hm0D, hm0a⟩ := (evalClause_literal_iff a D).mp (haN D hD)
        rcases m0 with ⟨p0, v0⟩
        by_cases hv0 : v0 = v
        · -- `D` was satisfied through the variable of `l`, so it holds the complement of `l`
          subst hv0
          have hp0 : p0 = !pol := by
            simp only [evalLiteral, decide_eq_true_eq] at hm0a
            rw [← hm0a, hav0]
          subst hp0
          obtain ⟨⟨mp, mv⟩, hmC, hml, hmD⟩ := hblk D hD hm0D
          have hmfalse := hCfalse (mp, mv) hmC
          have hmv : mv ≠ v0 := by
            intro heq
            subst heq
            apply hml
            simp only [evalLiteral, decide_eq_false_iff_not, hav0] at hmfalse
            cases mp <;> cases pol <;> simp_all
          refine (evalClause_literal_iff a' D).mpr ⟨(!mp, mv), hmD, ?_⟩
          simp only [evalLiteral, decide_eq_false_iff_not] at hmfalse
          simp only [evalLiteral, decide_eq_true_eq, ha_ne mv hmv]
          cases h : evalVar a mv <;> cases mp <;> simp_all
        · refine (evalClause_literal_iff a' D).mpr ⟨(p0, v0), hm0D, ?_⟩
          simp only [evalLiteral] at hm0a ⊢
          rw [ha_ne v0 hv0]
          exact hm0a
