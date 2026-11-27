import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

/-- A clause `C` padded with every sign pattern over a list of variables `zs` is equivalent to `C`
(vendored model). -/
theorem PvsNP.Units.m3_y_pad_clause_all_signs :
    ∀ (a : assgn) (C : clause) (zs : List var),
      evalCnf a (zs.sublists.map (fun T => C ++ zs.map (fun z => (decide (z ∈ T), z)))) =
        evalClause a C := by
  intro a C zs
  cases hC : evalClause a C with
  | true =>
    rw [evalCnf_clause_iff]
    intro D hD
    rw [List.mem_map] at hD
    obtain ⟨T, _, rfl⟩ := hD
    obtain ⟨l, hlC, hl⟩ := (evalClause_literal_iff a C).mp hC
    exact (evalClause_literal_iff a _).mpr ⟨l, List.mem_append_left _ hlC, hl⟩
  | false =>
    cases hN : evalCnf a (zs.sublists.map (fun T => C ++ zs.map (fun z => (decide (z ∈ T), z)))) with
    | false => rfl
    | true =>
      exfalso
      let T : List var := zs.filter (fun z => decide (z ∉ a))
      have hTsub : T ∈ zs.sublists := List.mem_sublists.mpr List.filter_sublist
      have hDT : C ++ zs.map (fun z => (decide (z ∈ T), z)) ∈
          zs.sublists.map (fun T => C ++ zs.map (fun z => (decide (z ∈ T), z))) :=
        List.mem_map.mpr ⟨T, hTsub, rfl⟩
      have hcl : evalClause a (C ++ zs.map (fun z => (decide (z ∈ T), z))) = true :=
        (evalCnf_clause_iff a _).mp hN _ hDT
      obtain ⟨l, hl, hlt⟩ := (evalClause_literal_iff a _).mp hcl
      rcases List.mem_append.mp hl with hlC | hlpad
      · have hCtrue : evalClause a C = true := (evalClause_literal_iff a C).mpr ⟨l, hlC, hlt⟩
        rw [hC] at hCtrue
        cases hCtrue
      · rw [List.mem_map] at hlpad
        obtain ⟨z, hzs, rfl⟩ := hlpad
        simp only [evalLiteral, evalVar] at hlt
        have hmemT : z ∈ T ↔ z ∉ a := by
          simp only [T, List.mem_filter, decide_eq_true_eq, hzs, true_and]
        by_cases hza : z ∈ a
        · have hzT : z ∈ T := by
            simp only [hza, decide_true] at hlt
            by_contra hnot
            simp [hnot] at hlt
          exact (hmemT.mp hzT) hza
        · have hzT : z ∈ T := hmemT.mpr hza
          simp [hza, hzT] at hlt
