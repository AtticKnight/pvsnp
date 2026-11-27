import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_dp_elimination

private theorem evalClause_iff (a : assgn) (C : clause) :
    evalClause a C = true ↔ ∃ l ∈ C, evalLiteral a l = true := by
  simp only [evalClause, List.any_eq_true]

private theorem evalCnf_iff (a : assgn) (N : cnf) :
    evalCnf a N = true ↔ ∀ C ∈ N, evalClause a C = true := by
  simp only [evalCnf, List.all_eq_true]

private theorem evalVar_cons_ne (a : assgn) (v w : var) (h : w ≠ v) :
    evalVar (v :: a) w = evalVar a w := by
  simp only [evalVar, List.mem_cons, h, false_or]

private theorem evalVar_filter_ne (a : assgn) (v w : var) (h : w ≠ v) :
    evalVar (a.filter (· != v)) w = evalVar a w := by
  simp [evalVar, h]

private theorem evalLiteral_cons_ne (a : assgn) (v : var) (l : literal) (h : l.2 ≠ v) :
    evalLiteral (v :: a) l = evalLiteral a l := by
  simp only [evalLiteral, evalVar_cons_ne a v l.2 h]

private theorem evalLiteral_filter_ne (a : assgn) (v : var) (l : literal) (h : l.2 ≠ v) :
    evalLiteral (a.filter (· != v)) l = evalLiteral a l := by
  simp only [evalLiteral, evalVar_filter_ne a v l.2 h]

theorem main :
    ∀ (N : cnf) (v : var), (∀ C ∈ N, (true, v) ∈ C → (false, v) ∉ C) →
      (SAT N ↔
        SAT (N.filter (fun C => decide ((true, v) ∉ C ∧ (false, v) ∉ C)) ++
          (N.filter (fun C => decide ((true, v) ∈ C))).flatMap (fun C =>
            (N.filter (fun D => decide ((false, v) ∈ D))).map (fun D =>
              C.filter (fun l => decide (l.2 ≠ v)) ++ D.filter (fun l => decide (l.2 ≠ v)))))) := by
  intro N v hnotaut
  constructor
  · rintro ⟨a, ha⟩
    have ha' := (evalCnf_iff a N).1 ha
    refine ⟨a, (evalCnf_iff a _).2 ?_⟩
    intro R hR
    rw [List.mem_append] at hR
    rcases hR with hR | hR
    · rw [List.mem_filter] at hR
      exact ha' R hR.1
    · rw [List.mem_flatMap] at hR
      obtain ⟨C, hC, hR⟩ := hR
      rw [List.mem_filter, decide_eq_true_eq] at hC
      rw [List.mem_map] at hR
      obtain ⟨D, hD, rfl⟩ := hR
      rw [List.mem_filter, decide_eq_true_eq] at hD
      rw [evalClause_iff]
      cases hav : evalVar a v with
      | true =>
        obtain ⟨l, hlD, hla⟩ := (evalClause_iff a D).1 (ha' D hD.1)
        have hne : l.2 ≠ v := by
          intro heq
          rcases l with ⟨pol, w⟩
          dsimp only at heq
          subst heq
          cases pol with
          | true => exact hnotaut D hD.1 hlD hD.2
          | false =>
            simp only [evalLiteral, hav, decide_eq_true_eq] at hla
            exact Bool.noConfusion hla
        exact ⟨l, List.mem_append_right _ (List.mem_filter.2 ⟨hlD, decide_eq_true hne⟩), hla⟩
      | false =>
        obtain ⟨l, hlC, hla⟩ := (evalClause_iff a C).1 (ha' C hC.1)
        have hne : l.2 ≠ v := by
          intro heq
          rcases l with ⟨pol, w⟩
          dsimp only at heq
          subst heq
          cases pol with
          | false => exact hnotaut C hC.1 hC.2 hlC
          | true =>
            simp only [evalLiteral, hav, decide_eq_true_eq] at hla
            exact Bool.noConfusion hla
        exact ⟨l, List.mem_append_left _ (List.mem_filter.2 ⟨hlC, decide_eq_true hne⟩), hla⟩
  · rintro ⟨a, ha⟩
    have ha' := (evalCnf_iff a _).1 ha
    by_cases hallD : ∀ D ∈ N, (false, v) ∈ D → ∃ l ∈ D, l.2 ≠ v ∧ evalLiteral a l = true
    · refine ⟨v :: a, (evalCnf_iff _ N).2 ?_⟩
      intro C hC
      rw [evalClause_iff]
      by_cases hpos : (true, v) ∈ C
      · exact ⟨(true, v), hpos, by simp [evalLiteral, evalVar]⟩
      · by_cases hneg : (false, v) ∈ C
        · obtain ⟨l, hlC, hne, hla⟩ := hallD C hC hneg
          exact ⟨l, hlC, by rwa [evalLiteral_cons_ne a v l hne]⟩
        · have hCmem : C ∈ N.filter (fun C => decide ((true, v) ∉ C ∧ (false, v) ∉ C)) :=
            List.mem_filter.2 ⟨hC, decide_eq_true ⟨hpos, hneg⟩⟩
          obtain ⟨l, hlC, hla⟩ := (evalClause_iff a C).1 (ha' C (List.mem_append_left _ hCmem))
          have hne : l.2 ≠ v := by
            intro heq
            rcases l with ⟨pol, w⟩
            dsimp only at heq
            subst heq
            cases pol <;> simp_all
          exact ⟨l, hlC, by rwa [evalLiteral_cons_ne a v l hne]⟩
    · push_neg at hallD
      obtain ⟨D₀, hD₀N, hD₀neg, hD₀fail⟩ := hallD
      refine ⟨a.filter (· != v), (evalCnf_iff _ N).2 ?_⟩
      intro C hC
      rw [evalClause_iff]
      by_cases hneg : (false, v) ∈ C
      · exact ⟨(false, v), hneg, by simp [evalLiteral, evalVar]⟩
      · by_cases hpos : (true, v) ∈ C
        · have hRmem : C.filter (fun l => decide (l.2 ≠ v)) ++ D₀.filter (fun l => decide (l.2 ≠ v)) ∈
              (N.filter (fun C => decide ((true, v) ∈ C))).flatMap (fun C =>
                (N.filter (fun D => decide ((false, v) ∈ D))).map (fun D =>
                  C.filter (fun l => decide (l.2 ≠ v)) ++ D.filter (fun l => decide (l.2 ≠ v)))) := by
            rw [List.mem_flatMap]
            exact ⟨C, List.mem_filter.2 ⟨hC, decide_eq_true hpos⟩,
              List.mem_map.2 ⟨D₀, List.mem_filter.2 ⟨hD₀N, decide_eq_true hD₀neg⟩, rfl⟩⟩
          obtain ⟨l, hlR, hla⟩ := (evalClause_iff a _).1 (ha' _ (List.mem_append_right _ hRmem))
          rw [List.mem_append] at hlR
          rcases hlR with hlC | hlD
          · rw [List.mem_filter, decide_eq_true_eq] at hlC
            exact ⟨l, hlC.1, by rwa [evalLiteral_filter_ne a v l hlC.2]⟩
          · rw [List.mem_filter, decide_eq_true_eq] at hlD
            exact absurd hla (hD₀fail l hlD.1 hlD.2)
        · have hCmem : C ∈ N.filter (fun C => decide ((true, v) ∉ C ∧ (false, v) ∉ C)) :=
            List.mem_filter.2 ⟨hC, decide_eq_true ⟨hpos, hneg⟩⟩
          obtain ⟨l, hlC, hla⟩ := (evalClause_iff a C).1 (ha' C (List.mem_append_left _ hCmem))
          have hne : l.2 ≠ v := by
            intro heq
            rcases l with ⟨pol, w⟩
            dsimp only at heq
            subst heq
            cases pol <;> simp_all
          exact ⟨l, hlC, by rwa [evalLiteral_filter_ne a v l hne]⟩

end PvsNP.Units.m3_dp_elimination

theorem PvsNP.Units.m3_dp_elimination :
    ∀ (N : cnf) (v : var), (∀ C ∈ N, (true, v) ∈ C → (false, v) ∉ C) →
      (SAT N ↔
        SAT (N.filter (fun C => decide ((true, v) ∉ C ∧ (false, v) ∉ C)) ++
          (N.filter (fun C => decide ((true, v) ∈ C))).flatMap (fun C =>
            (N.filter (fun D => decide ((false, v) ∈ D))).map (fun D =>
              C.filter (fun l => decide (l.2 ≠ v)) ++ D.filter (fun l => decide (l.2 ≠ v)))))) :=
  PvsNP.Units.m3_dp_elimination.main
