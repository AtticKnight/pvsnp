import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_y_resolution_derivation_sound :
  ∀ (N : cnf) (L : List clause),
    (∀ i < L.length, L.getD i [] ∈ N ∨ ∃ j < i, ∃ k < i, ∃ v : var, (true, v) ∈ L.getD j [] ∧ (false, v) ∈ L.getD k [] ∧
      L.getD i [] = (L.getD j []).filter (fun l => decide (l ≠ (true, v))) ++ (L.getD k []).filter (fun l => decide (l ≠ (false, v)))) →
    [] ∈ L → ¬ SAT N := by
  intro N L hderiv hnil hsat
  obtain ⟨a, ha⟩ := hsat
  rw [satisfiesCnf, evalCnf_clause_iff] at ha
  have hall : ∀ i, i < L.length → evalClause a (L.getD i []) = true := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      intro hi
      rcases hderiv i hi with hmem | ⟨j, hjlt, k, hklt, v, _, _, heq⟩
      · exact ha _ hmem
      · have hj : evalClause a (L.getD j []) = true := ih j hjlt (Nat.lt_trans hjlt hi)
        have hk : evalClause a (L.getD k []) = true := ih k hklt (Nat.lt_trans hklt hi)
        rw [heq, evalClause_literal_iff]
        cases hv : evalVar a v with
        | true =>
          obtain ⟨l, hlmem, hlval⟩ := (evalClause_literal_iff a _).mp hk
          have hlne : l ≠ (false, v) := by
            intro h
            subst h
            simp only [evalLiteral, hv] at hlval
            cases hlval
          refine ⟨l, List.mem_append_right _ ?_, hlval⟩
          exact List.mem_filter.mpr ⟨hlmem, decide_eq_true hlne⟩
        | false =>
          obtain ⟨l, hlmem, hlval⟩ := (evalClause_literal_iff a _).mp hj
          have hlne : l ≠ (true, v) := by
            intro h
            subst h
            simp only [evalLiteral, hv] at hlval
            cases hlval
          refine ⟨l, List.mem_append_left _ ?_, hlval⟩
          exact List.mem_filter.mpr ⟨hlmem, decide_eq_true hlne⟩
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hnil
  have hci : evalClause a (L.getD i []) = true := hall i hi
  have hgd : L.getD i [] = [] := by
    simp [List.getD, hi, hget]
  rw [hgd] at hci
  cases hci
