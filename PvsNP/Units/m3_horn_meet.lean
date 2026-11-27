import Mathlib
import PvsNP.Defs
import CookLevin

theorem PvsNP.Units.m3_horn_meet :
    ∀ (N : cnf) (a b : assgn), (∀ C ∈ N, (C.filter (fun l => l.1)).length ≤ 1) →
      satisfiesCnf a N → satisfiesCnf b N →
      satisfiesCnf (a.filter (fun v => decide (v ∈ b))) N := by
  intro N a b hHorn ha hb
  set c := a.filter (fun v => decide (v ∈ b)) with hc
  have hmem : ∀ u, u ∈ c ↔ u ∈ a ∧ u ∈ b := by
    intro u
    simp only [hc, List.mem_filter, decide_eq_true_eq]
  refine (evalCnf_clause_iff _ _).mpr ?_
  intro C hC
  have haC := (evalCnf_clause_iff a N).mp ha C hC
  have hbC := (evalCnf_clause_iff b N).mp hb C hC
  obtain ⟨⟨s, v⟩, hlC, hla⟩ := (evalClause_literal_iff a C).mp haC
  obtain ⟨⟨s', v'⟩, hl'C, hlb⟩ := (evalClause_literal_iff b C).mp hbC
  cases s with
  | false =>
      -- The witness under `a` is negative: it stays true under the smaller assignment `c`.
      have hvna : v ∉ a := by
        by_contra! hv
        simp [evalLiteral, evalVar, hv] at hla
      have hvnc : v ∉ c := fun hvc => hvna ((hmem v).mp hvc).1
      refine (evalClause_literal_iff c C).mpr ⟨(false, v), hlC, ?_⟩
      simp [evalLiteral, evalVar, hvnc]
  | true =>
      cases s' with
      | false =>
          -- The witness under `b` is negative: it stays true under `c ⊆ b`.
          have hvn'b : v' ∉ b := by
            by_contra! hv
            simp [evalLiteral, evalVar, hv] at hlb
          have hvnc : v' ∉ c := fun hvc => hvn'b ((hmem v').mp hvc).2
          refine (evalClause_literal_iff c C).mpr ⟨(false, v'), hl'C, ?_⟩
          simp [evalLiteral, evalVar, hvnc]
      | true =>
          -- Both witnesses are positive, so both are the clause's one positive literal.
          have hva : v ∈ a := by
            by_contra hv
            simp [evalLiteral, evalVar, hv] at hla
          have hv'b : v' ∈ b := by
            by_contra hv
            simp [evalLiteral, evalVar, hv] at hlb
          have hvv : v = v' := by
            have hle : (C.filter (fun l => l.1)).length ≤ 1 := hHorn C hC
            have hm1 : (true, v) ∈ C.filter (fun l => l.1) :=
              List.mem_filter.mpr ⟨hlC, rfl⟩
            have hm2 : (true, v') ∈ C.filter (fun l => l.1) :=
              List.mem_filter.mpr ⟨hl'C, rfl⟩
            rcases hF : C.filter (fun l => l.1) with _ | ⟨x, xs⟩
            · rw [hF] at hm1
              simp at hm1
            · rw [hF] at hle hm1 hm2
              have hxs : xs = [] := by
                by_contra hne
                obtain ⟨y, ys, rfl⟩ : ∃ y ys, xs = y :: ys :=
                  List.exists_cons_of_ne_nil hne
                simp only [List.length_cons] at hle
                omega
              subst hxs
              rw [List.mem_singleton] at hm1 hm2
              have hEq : (true, v) = (true, v') := hm1.trans hm2.symm
              exact congrArg Prod.snd hEq
          have hvb : v ∈ b := by
            rw [hvv]
            exact hv'b
          have hvc : v ∈ c := List.mem_filter.mpr ⟨hva, decide_eq_true hvb⟩
          refine (evalClause_literal_iff c C).mpr ⟨(true, v), hlC, ?_⟩
          simp [evalLiteral, evalVar, hvc]
