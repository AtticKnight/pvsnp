import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_amo_sequential_counter

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

end PvsNP.Units.m3_amo_sequential_counter

namespace PvsNP.Units.m3_amo_sequential_counter

theorem cl_imp (b : assgn) (u w : var) :
    evalClause b [(false, u), (true, w)] = true ↔ (u ∈ b → w ∈ b) := by
  by_cases hu : u ∈ b <;> by_cases hw : w ∈ b <;> simp [evalClause, evalLiteral, evalVar, hu, hw]

theorem cl_nand (b : assgn) (u w : var) :
    evalClause b [(false, u), (false, w)] = true ↔ ¬ (u ∈ b ∧ w ∈ b) := by
  by_cases hu : u ∈ b <;> by_cases hw : w ∈ b <;> simp [evalClause, evalLiteral, evalVar, hu, hw]

/-- The sequential-counter clauses: `x_i → s_i`, `s_i → s_{i+1}`, `x_{i+1} → ¬ s_i`, with
`x_i = 2 i` and `s_i = 2 i + 1`. -/
def seqCnf (n : ℕ) : cnf :=
  (List.range n).map (fun i => [(false, 2 * i), (true, 2 * i + 1)]) ++
    (List.range (n - 1)).flatMap (fun i =>
      [[(false, 2 * i + 1), (true, 2 * i + 3)], [(false, 2 * i + 2), (false, 2 * i + 1)]])

theorem sat_iff (n : ℕ) (b : assgn) :
    satisfiesCnf b (seqCnf n) ↔
      (∀ i < n, 2 * i ∈ b → 2 * i + 1 ∈ b) ∧
      (∀ i < n - 1, 2 * i + 1 ∈ b → 2 * i + 3 ∈ b) ∧
      (∀ i < n - 1, ¬ (2 * i + 2 ∈ b ∧ 2 * i + 1 ∈ b)) := by
  unfold satisfiesCnf
  rw [evalCnf_clause_iff]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · exact (cl_imp b _ _).1
        (h _ (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))
    · exact (cl_imp b _ _).1
        (h _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp⟩)))
    · exact (cl_nand b _ _).1
        (h _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by simp⟩)))
  · rintro ⟨h1, h2, h3⟩ C hC
    rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hC
      exact (cl_imp b _ _).2 (h1 i (List.mem_range.1 hi))
    · obtain ⟨i, hi, hC⟩ := List.mem_flatMap.1 hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl
      · exact (cl_imp b _ _).2 (h2 i (List.mem_range.1 hi))
      · exact (cl_nand b _ _).2 (h3 i (List.mem_range.1 hi))

theorem chain {n : ℕ} {b : assgn} (h2 : ∀ i < n - 1, 2 * i + 1 ∈ b → 2 * i + 3 ∈ b) {j : ℕ}
    (hj : 2 * j + 1 ∈ b) : ∀ m, j + m < n → 2 * (j + m) + 1 ∈ b := by
  intro m
  induction m with
  | zero => intro _; simpa using hj
  | succ m ih =>
    intro hm
    have h := h2 (j + m) (by omega) (ih (by omega))
    have e : 2 * (j + (m + 1)) + 1 = 2 * (j + m) + 3 := by ring
    rw [e]
    exact h

theorem len_le_one_of {l : List ℕ} (hn : l.Nodup) (h : ∀ x ∈ l, ∀ y ∈ l, x = y) :
    l.length ≤ 1 := by
  match l, hn, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | x :: y :: r, hn, h =>
    exfalso
    have hxy := h x (by simp) y (by simp)
    have hx : x ∉ y :: r := (List.nodup_cons.1 hn).1
    exact hx (by simp [hxy])

theorem eq_of_len_le_one {l : List ℕ} (h : l.length ≤ 1) : ∀ x ∈ l, ∀ y ∈ l, x = y := by
  match l, h with
  | [], _ => simp
  | [_], _ => simp
  | _ :: _ :: _, h => simp at h

/-- The counter assignment: the true originals, and `s_i` whenever an original at or before `i`
is true. -/
def seqB (n : ℕ) (a : assgn) : assgn :=
  ((List.range n).filter (fun i => decide (2 * i ∈ a))).map (fun i => 2 * i) ++
    ((List.range n).filter (fun i => (List.range (i + 1)).any (fun j => decide (2 * j ∈ a)))).map
      (fun i => 2 * i + 1)

theorem mem_even (n : ℕ) (a : assgn) (i : ℕ) : 2 * i ∈ seqB n a ↔ i < n ∧ 2 * i ∈ a := by
  simp only [seqB, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro (⟨j, ⟨hj, ha⟩, he⟩ | ⟨j, _, he⟩)
    · have : j = i := by omega
      subst this
      exact ⟨hj, ha⟩
    · omega
  · rintro ⟨hi, ha⟩
    exact Or.inl ⟨i, ⟨hi, ha⟩, rfl⟩

theorem mem_odd (n : ℕ) (a : assgn) (i : ℕ) :
    2 * i + 1 ∈ seqB n a ↔ i < n ∧ ∃ j ≤ i, 2 * j ∈ a := by
  simp only [seqB, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
    decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro (⟨j, _, he⟩ | ⟨j, ⟨hj, k, hk, ha⟩, he⟩)
    · omega
    · have : j = i := by omega
      subst this
      exact ⟨hj, k, by omega, ha⟩
  · rintro ⟨hi, k, hk, ha⟩
    exact Or.inr ⟨i, ⟨hi, k, by omega, ha⟩, rfl⟩

end PvsNP.Units.m3_amo_sequential_counter

/-- The sequential-counter encoding of "at most one": its clauses have a model agreeing with `a`
on the originals exactly when at most one original is true in `a`. -/
theorem PvsNP.Units.m3_amo_sequential_counter :
    ∀ (n : ℕ) (a : assgn),
      (∃ b : assgn, (∀ i < n, (2 * i ∈ b ↔ 2 * i ∈ a)) ∧
        satisfiesCnf b ((List.range n).map (fun i => [(false, 2 * i), (true, 2 * i + 1)]) ++
          (List.range (n - 1)).flatMap (fun i =>
            [[(false, 2 * i + 1), (true, 2 * i + 3)], [(false, 2 * i + 2), (false, 2 * i + 1)]]))) ↔
        ((List.range n).filter (fun i => decide (2 * i ∈ a))).length ≤ 1 := by
  intro n a
  show (∃ b : assgn, (∀ i < n, (2 * i ∈ b ↔ 2 * i ∈ a)) ∧
    satisfiesCnf b (PvsNP.Units.m3_amo_sequential_counter.seqCnf n)) ↔ _
  constructor
  · rintro ⟨b, hag, hs⟩
    obtain ⟨h1, h2, h3⟩ := (PvsNP.Units.m3_amo_sequential_counter.sat_iff n b).1 hs
    have key : ∀ j k, j < k → k < n → 2 * j ∈ a → 2 * k ∈ a → False := by
      intro j k hjk hk ha hb
      have sj := h1 j (by omega) ((hag j (by omega)).2 ha)
      have sk1 := PvsNP.Units.m3_amo_sequential_counter.chain h2 sj (k - 1 - j) (by omega)
      have e : j + (k - 1 - j) = k - 1 := by omega
      rw [e] at sk1
      have hx : 2 * (k - 1) + 2 ∈ b := by
        have e2 : 2 * (k - 1) + 2 = 2 * k := by omega
        rw [e2]
        exact (hag k hk).2 hb
      exact h3 (k - 1) (by omega) ⟨hx, sk1⟩
    refine PvsNP.Units.m3_amo_sequential_counter.len_le_one_of (List.nodup_range.filter _) fun j hj k hk => ?_
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj hk
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact key j k hlt hk.1 hj.2 hk.2
    · exact key k j hlt hj.1 hk.2 hj.2
  · intro hc
    have hu := PvsNP.Units.m3_amo_sequential_counter.eq_of_len_le_one hc
    have inS : ∀ i, i < n → 2 * i ∈ a →
        i ∈ (List.range n).filter (fun i => decide (2 * i ∈ a)) := fun i hi ha =>
      List.mem_filter.2 ⟨List.mem_range.2 hi, by simpa using ha⟩
    refine ⟨PvsNP.Units.m3_amo_sequential_counter.seqB n a, fun i hi => ?_, (PvsNP.Units.m3_amo_sequential_counter.sat_iff n _).2 ⟨?_, ?_, ?_⟩⟩
    · rw [PvsNP.Units.m3_amo_sequential_counter.mem_even]
      exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩
    · intro i hi h
      rw [PvsNP.Units.m3_amo_sequential_counter.mem_even] at h
      rw [PvsNP.Units.m3_amo_sequential_counter.mem_odd]
      exact ⟨hi, i, le_rfl, h.2⟩
    · intro i hi h
      rw [PvsNP.Units.m3_amo_sequential_counter.mem_odd] at h
      have e : 2 * i + 3 = 2 * (i + 1) + 1 := by ring
      rw [e, PvsNP.Units.m3_amo_sequential_counter.mem_odd]
      obtain ⟨_, j, hj, ha⟩ := h
      exact ⟨by omega, j, by omega, ha⟩
    · rintro i hi ⟨hx, hs⟩
      have e : 2 * i + 2 = 2 * (i + 1) := by ring
      rw [e, PvsNP.Units.m3_amo_sequential_counter.mem_even] at hx
      rw [PvsNP.Units.m3_amo_sequential_counter.mem_odd] at hs
      obtain ⟨hi1, ha1⟩ := hx
      obtain ⟨_, j, hj, haj⟩ := hs
      have := hu (i + 1) (inS _ hi1 ha1) j (inS j (by omega) haj)
      omega
