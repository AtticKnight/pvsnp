import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_positive_cnf_sat_iff

section logic

/-- A literal is true exactly when its variable's value is its sign. -/
theorem evalLiteral_iff (a : assgn) (s : Bool) (v : var) :
    evalLiteral a (s, v) = true ↔ evalVar a v = s := by
  simp [evalLiteral]

/-- The assignment `a` with variable `v` set to `b`. -/
def setVar (a : assgn) (v : var) (b : Bool) : assgn :=
  if b then v :: a else a.filter (fun w => w ≠ v)

theorem evalVar_setVar_self (a : assgn) (v : var) (b : Bool) :
    evalVar (setVar a v b) v = b := by
  cases b <;> simp [setVar, evalVar]

theorem evalVar_setVar_ne (a : assgn) (v w : var) (b : Bool) (h : w ≠ v) :
    evalVar (setVar a v b) w = evalVar a w := by
  cases b <;> simp [setVar, evalVar, h]

/-- Changing a variable a clause does not mention leaves the clause's value. -/
theorem evalClause_setVar (a : assgn) (v : var) (b : Bool) (C : clause)
    (hC : ∀ l ∈ C, l.2 ≠ v) : evalClause (setVar a v b) C = evalClause a C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    obtain ⟨s, w⟩ := l
    have hw : w ≠ v := hC (s, w) (by simp)
    have ih' := ih (fun l hl => hC l (List.mem_cons_of_mem _ hl))
    simp only [evalClause, List.any_cons] at ih' ⊢
    rw [ih']
    simp [evalLiteral, evalVar_setVar_ne a v w b hw]

/-- A CNF with the empty clause is unsatisfiable. -/
theorem empty_clause_unsat (N : cnf) (h : [] ∈ N) : ¬ SAT N := by
  rintro ⟨a, ha⟩
  have := (evalCnf_clause_iff a N).1 ha [] h
  simp [evalClause] at this

/-- The resolution rule is sound. -/
theorem resolution_sound (a : assgn) (C D : clause) (v : var)
    (h₁ : evalClause a ((true, v) :: C) = true) (h₂ : evalClause a ((false, v) :: D) = true) :
    evalClause a (C ++ D) = true := by
  simp only [evalClause, List.any_cons, List.any_append, Bool.or_eq_true] at h₁ h₂ ⊢
  cases hv : evalVar a v
  · rcases h₁ with h | h
    · simp [evalLiteral, hv] at h
    · exact Or.inl h
  · rcases h₂ with h | h
    · simp [evalLiteral, hv] at h
    · exact Or.inr h

/-- Every variable of a literal of a clause of `N` is in `varsOfCnf N`. -/
theorem mem_varsOfCnf {N : cnf} {C : clause} {l : literal} (hC : C ∈ N) (hl : l ∈ C) :
    l.2 ∈ SAT_inNP.varsOfCnf N := by
  unfold SAT_inNP.varsOfCnf SAT_inNP.varsOfClause
  refine List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨C, hC, rfl⟩, ?_⟩
  exact List.mem_flatten.2 ⟨[l.2], List.mem_map.2 ⟨l, hl, rfl⟩, List.mem_singleton_self _⟩

/-- A CNF whose every clause has a positive literal is satisfiable: make every variable true. -/
theorem positive_clause_sat (N : cnf) (h : ∀ C ∈ N, ∃ v : var, (true, v) ∈ C) : SAT N := by
  refine ⟨SAT_inNP.varsOfCnf N, (evalCnf_clause_iff _ N).2 fun C hC => ?_⟩
  obtain ⟨v, hv⟩ := h C hC
  refine (evalClause_literal_iff _ C).2 ⟨(true, v), hv, ?_⟩
  have := mem_varsOfCnf hC hv
  simp [evalLiteral, evalVar, this]

/-- Splitting on a variable preserves satisfiability. -/
theorem split_rule (N : cnf) (v : var) :
    SAT N ↔ (SAT ([(true, v)] :: N) ∨ SAT ([(false, v)] :: N)) := by
  constructor
  · rintro ⟨a, ha⟩
    cases hv : evalVar a v
    · right
      exact ⟨a, by simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, hv] at ha ⊢; exact ha⟩
    · left
      exact ⟨a, by simp [satisfiesCnf, evalCnf, evalClause, evalLiteral, hv] at ha ⊢; exact ha⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact ⟨a, by simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha; exact ha.2⟩
    · exact ⟨a, by simp only [satisfiesCnf, evalCnf, List.all_cons, Bool.and_eq_true] at ha; exact ha.2⟩

/-- Satisfiability is monotone along sublists of clauses. -/
theorem sat_of_subset {N M : cnf} (h : ∀ C ∈ M, C ∈ N) : SAT N → SAT M := by
  rintro ⟨a, ha⟩
  exact ⟨a, (evalCnf_clause_iff a M).2 fun C hC => (evalCnf_clause_iff a N).1 ha C (h C hC)⟩

/-- The pure literal rule preserves satisfiability. -/
theorem pure_literal (N : cnf) (l : literal) (hp : ∀ C ∈ N, (!l.1, l.2) ∉ C) :
    SAT N ↔ SAT (N.filter (fun C => decide (l ∉ C))) := by
  constructor
  · exact sat_of_subset fun C hC => (List.mem_filter.1 hC).1
  · rintro ⟨a, ha⟩
    refine ⟨setVar a l.2 l.1, (evalCnf_clause_iff _ N).2 fun C hC => ?_⟩
    by_cases hl : l ∈ C
    · refine (evalClause_literal_iff _ C).2 ⟨l, hl, ?_⟩
      obtain ⟨s, w⟩ := l
      exact (evalLiteral_iff _ _ _).2 (evalVar_setVar_self _ _ _)
    · have hf : C ∈ N.filter (fun C => decide (l ∉ C)) := List.mem_filter.2 ⟨hC, by simp [hl]⟩
      have hCa := (evalCnf_clause_iff a _).1 ha C hf
      rw [evalClause_setVar]
      · exact hCa
      · intro m hm heq
        obtain ⟨s, w⟩ := m
        obtain ⟨t, u⟩ := l
        simp only at heq
        subst heq
        cases s <;> cases t
        · exact hl hm
        · exact hp C hC (by simpa using hm)
        · exact hp C hC (by simpa using hm)
        · exact hl hm

end logic

end PvsNP.Units.m3_positive_cnf_sat_iff

/-- A CNF of positive literals is satisfiable exactly when it has no empty clause: the empty
clause is unsatisfiable, and otherwise making every variable true satisfies each clause. -/
theorem PvsNP.Units.m3_positive_cnf_sat_iff :
    ∀ N : cnf, (∀ C ∈ N, ∀ l ∈ C, l.1 = true) → (SAT N ↔ [] ∉ N) := by
  intro N hpos
  constructor
  · intro hs he
    exact PvsNP.Units.m3_positive_cnf_sat_iff.empty_clause_unsat N he hs
  · intro hne
    apply PvsNP.Units.m3_positive_cnf_sat_iff.positive_clause_sat
    intro C hC
    cases C with
    | nil => exact absurd hC hne
    | cons l r =>
      refine ⟨l.2, ?_⟩
      have h1 := hpos _ hC l (by simp)
      obtain ⟨s, v⟩ := l
      simp only at h1
      subst h1
      simp
