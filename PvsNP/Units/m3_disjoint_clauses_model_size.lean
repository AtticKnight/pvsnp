import Mathlib
import PvsNP.Defs
import CookLevin

open CookLevin CookLevin.Lang EvalCnfCmd CnfWellFormed

namespace PvsNP.Units.m3_disjoint_clauses_model_size

/-- A satisfied all-positive clause contributes a variable of `a` occurring in it. -/
theorem exists_var_of_sat {C : clause} {a : assgn}
    (hpos : ∀ l ∈ C, l.1 = true) (hsat : evalClause a C = true) :
    ∃ v, v ∈ a ∧ (true, v) ∈ C := by
  obtain ⟨l, hlC, hl⟩ := (evalClause_literal_iff a C).mp hsat
  obtain ⟨s, v⟩ := l
  have hs : s = true := hpos (s, v) hlC
  subst hs
  refine ⟨v, ?_, hlC⟩
  simpa [evalLiteral, evalVar] using hl

end PvsNP.Units.m3_disjoint_clauses_model_size

open PvsNP.Units.m3_disjoint_clauses_model_size

theorem PvsNP.Units.m3_disjoint_clauses_model_size :
    ∀ (N : cnf) (a : assgn), (∀ C ∈ N, ∀ l ∈ C, l.1 = true) →
      N.Pairwise (fun C D => ∀ l ∈ C, ∀ m ∈ D, l.2 ≠ m.2) →
      satisfiesCnf a N → N.length ≤ a.length := by
  intro N
  induction N with
  | nil =>
    intro a _ _ _
    simp
  | cons C N ih =>
    intro a hpos hpair hsat
    -- Split the hypotheses between the head clause and the tail.
    have hposC : ∀ l ∈ C, l.1 = true :=
      fun l hl => hpos C List.mem_cons_self l hl
    have hposN : ∀ D ∈ N, ∀ l ∈ D, l.1 = true :=
      fun D hD l hl => hpos D (List.mem_cons_of_mem C hD) l hl
    obtain ⟨hCD, hpairN⟩ := List.pairwise_cons.mp hpair
    have hsatC : evalClause a C = true :=
      (evalCnf_clause_iff a (C :: N)).mp hsat C List.mem_cons_self
    -- The head clause contributes one variable `v` of `a`.
    obtain ⟨v, hva, hvC⟩ := exists_var_of_sat hposC hsatC
    -- Apply the induction hypothesis to the tail with `v` erased from `a`.
    have hlen : N.length ≤ (a.erase v).length := by
      apply ih (a.erase v)
      · exact hposN
      · exact hpairN
      · rw [satisfiesCnf, evalCnf_clause_iff]
        intro D hD
        have hsatD : evalClause a D = true :=
          (evalCnf_clause_iff a (C :: N)).mp hsat D (List.mem_cons_of_mem C hD)
        obtain ⟨w, hwa, hwD⟩ := exists_var_of_sat (hposN D hD) hsatD
        -- The witness `w` of `D` differs from `v` by disjointness.
        have hne : w ≠ v := by
          have h := hCD D hD (true, v) hvC (true, w) hwD
          exact Ne.symm h
        have hw' : w ∈ a.erase v := (List.mem_erase_of_ne hne).mpr hwa
        refine (evalClause_literal_iff _ D).mpr ⟨(true, w), hwD, ?_⟩
        simpa [evalLiteral, evalVar, hw']
    have hlen2 : (a.erase v).length = a.length - 1 := List.length_erase_of_mem hva
    have hpos_len : 0 < a.length := List.length_pos_of_mem hva
    simp only [List.length_cons]
    omega
