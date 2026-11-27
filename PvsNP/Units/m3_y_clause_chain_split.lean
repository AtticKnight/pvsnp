import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_clause_chain_split

private theorem getD_eq_getElem (ls : List literal) (i : Nat) (hi : i < ls.length) :
    ls.getD i (true, 0) = ls[i] := by
  simp [List.getD, hi]

private theorem take_succ_eq (ls : List literal) (i : Nat) (hi : i < ls.length) :
    ls.take (i + 1) = ls.take i ++ [ls[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp

private theorem evalLiteral_congr (a a' : assgn) (l : literal)
    (h : evalVar a' l.2 = evalVar a l.2) :
    evalLiteral a' l = evalLiteral a l := by
  rcases l with ⟨s, v⟩
  simp only [evalLiteral]
  rw [h]

private theorem evalClause_congr (a a' : assgn) (C : clause)
    (h : ∀ l ∈ C, evalVar a' l.2 = evalVar a l.2) :
    evalClause a' C = evalClause a C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
    simp only [evalClause, List.any_cons]
    rw [evalLiteral_congr a a' l (h l List.mem_cons_self)]
    congr 1
    exact ih (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))

end PvsNP.Units.m3_y_clause_chain_split

theorem PvsNP.Units.m3_y_clause_chain_split :
  ∀ (N : cnf) (ls : List literal) (z : var), (∀ l ∈ ls, l.2 < z) → (∀ C ∈ N, ∀ l ∈ C, l.2 < z) →
    (SAT ([(false, z)] :: [(true, z + ls.length)] ::
        ((List.range ls.length).map (fun i => [(false, z + i + 1), (true, z + i), ls.getD i (true, 0)]) ++ N)) ↔
      SAT (ls :: N)) := by
  intro N ls z hls hN
  constructor
  · rintro ⟨a, ha⟩
    rw [satisfiesCnf, evalCnf_clause_iff] at ha
    have hz0 : evalVar a z = false := by
      have h := ha [(false, z)] (by simp)
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral,
        decide_eq_true_eq] at h
      exact h
    have hzm : evalVar a (z + ls.length) = true := by
      have h := ha [(true, z + ls.length)] (by simp)
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral,
        decide_eq_true_eq] at h
      exact h
    have hstep : ∀ i < ls.length,
        evalVar a (z + i + 1) = false ∨ evalVar a (z + i) = true ∨
          evalLiteral a (ls.getD i (true, 0)) = true := by
      intro i hi
      have hmem : [(false, z + i + 1), (true, z + i), ls.getD i (true, 0)] ∈
          [(false, z)] :: [(true, z + ls.length)] ::
            ((List.range ls.length).map (fun i => [(false, z + i + 1), (true, z + i), ls.getD i (true, 0)]) ++ N) := by
        refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left N ?_))
        exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
      have h := ha _ hmem
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at h
      rcases h with h1 | h2 | h3
      · left
        simp only [evalLiteral, decide_eq_true_eq] at h1
        exact h1
      · right; left
        simp only [evalLiteral, decide_eq_true_eq] at h2
        exact h2
      · exact Or.inr (Or.inr h3)
    have hNsat : ∀ C ∈ N, evalClause a C = true := by
      intro C hC
      exact ha C (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hC)))
    refine ⟨a, ?_⟩
    rw [satisfiesCnf, evalCnf_clause_iff]
    intro C hC
    rcases List.mem_cons.mp hC with hCls | hCN
    · rw [hCls]
      by_contra hfalse
      have hfls : evalClause a ls = false := Bool.eq_false_iff.mpr hfalse
      have hind : ∀ k ≤ ls.length, evalVar a (z + k) = false := by
        intro k
        induction k with
        | zero =>
          intro _
          simpa using hz0
        | succ k ih =>
          intro hk
          have hklt : k < ls.length := Nat.lt_of_succ_le hk
          have hprev : evalVar a (z + k) = false := ih (Nat.le_of_lt hklt)
          rcases hstep k hklt with h1 | h2 | h3
          · simpa [Nat.add_assoc] using h1
          · rw [hprev] at h2; cases h2
          · have hmeml : ls.getD k (true, 0) ∈ ls := by
              rw [PvsNP.Units.m3_y_clause_chain_split.getD_eq_getElem ls k hklt]
              exact List.getElem_mem hklt
            have htrue : evalClause a ls = true :=
              (evalClause_literal_iff a ls).mpr ⟨_, hmeml, h3⟩
            rw [hfls] at htrue; cases htrue
      have hbot := hind ls.length (Nat.le_refl _)
      rw [hzm] at hbot
      cases hbot
    · exact hNsat C hCN
  · rintro ⟨a, ha⟩
    rw [satisfiesCnf, evalCnf_clause_iff] at ha
    have hlssat : evalClause a ls = true := ha ls List.mem_cons_self
    let a' : assgn :=
      a.filter (fun v => decide (v < z)) ++
      ((List.range (ls.length + 1)).filter (fun i => evalClause a (ls.take i))).map (fun i => z + i)
    have heval_lt : ∀ v, v < z → evalVar a' v = evalVar a v := by
      intro v hv
      simp only [evalVar, decide_eq_decide]
      constructor
      · intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · exact (List.mem_filter.mp h1).1
        · rcases List.mem_map.mp h2 with ⟨i, _, hi⟩
          exact absurd (hi ▸ hv) (Nat.not_lt_of_ge (Nat.le_add_right z i))
      · intro hmem
        exact List.mem_append_left _ (List.mem_filter.mpr ⟨hmem, decide_eq_true hv⟩)
    have heval_z : ∀ i ≤ ls.length, evalVar a' (z + i) = evalClause a (ls.take i) := by
      intro i hi
      apply Bool.eq_iff_iff.mpr
      simp only [evalVar, decide_eq_true_eq]
      constructor
      · intro hmem
        rcases List.mem_append.mp hmem with h1 | h2
        · have hlt := of_decide_eq_true (List.mem_filter.mp h1).2
          exact absurd hlt (Nat.not_lt_of_ge (Nat.le_add_right z i))
        · rcases List.mem_map.mp h2 with ⟨j, hj, hjeq⟩
          have heq : j = i := Nat.add_left_cancel hjeq
          subst heq
          exact (List.mem_filter.mp hj).2
      · intro htake
        refine List.mem_append_right _ (List.mem_map.mpr ⟨i, ?_, rfl⟩)
        exact List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.lt_succ_of_le hi), htake⟩
    refine ⟨a', ?_⟩
    rw [satisfiesCnf, evalCnf_clause_iff]
    intro C hC
    rcases List.mem_cons.mp hC with hC0 | hC
    · rw [hC0]
      have h0 := heval_z 0 (Nat.zero_le _)
      simp only [Nat.add_zero, List.take_zero, evalClause, List.any_nil] at h0
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral,
        decide_eq_true_eq]
      exact h0
    rcases List.mem_cons.mp hC with hCm | hC
    · rw [hCm]
      have hm := heval_z ls.length (Nat.le_refl _)
      rw [List.take_length, hlssat] at hm
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, evalLiteral,
        decide_eq_true_eq]
      exact hm
    rcases List.mem_append.mp hC with hchain | hCN
    · rcases List.mem_map.mp hchain with ⟨i, hi, hCi⟩
      rw [← hCi]
      have hilt : i < ls.length := List.mem_range.mp hi
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
      cases hnext : evalClause a (ls.take (i + 1)) with
      | false =>
        left
        have h1 := heval_z (i + 1) (Nat.succ_le_of_lt hilt)
        rw [hnext] at h1
        simp only [evalLiteral, decide_eq_true_eq]
        simpa [Nat.add_assoc] using h1
      | true =>
        right
        cases hprev : evalClause a (ls.take i) with
        | true =>
          left
          have h0 := heval_z i (Nat.le_of_lt hilt)
          rw [hprev] at h0
          simp only [evalLiteral, decide_eq_true_eq]
          exact h0
        | false =>
          right
          rw [PvsNP.Units.m3_y_clause_chain_split.take_succ_eq ls i hilt] at hnext
          obtain ⟨l, hlmem, hlval⟩ := (evalClause_literal_iff a _).mp hnext
          rcases List.mem_append.mp hlmem with hl1 | hl2
          · have htr : evalClause a (ls.take i) = true :=
              (evalClause_literal_iff a _).mpr ⟨l, hl1, hlval⟩
            rw [hprev] at htr; cases htr
          · have hleq : l = ls[i] := List.mem_singleton.mp hl2
            subst hleq
            rw [PvsNP.Units.m3_y_clause_chain_split.getD_eq_getElem ls i hilt]
            rw [PvsNP.Units.m3_y_clause_chain_split.evalLiteral_congr a a' ls[i]
              (heval_lt _ (hls _ (List.getElem_mem hilt)))]
            exact hlval
    · rw [PvsNP.Units.m3_y_clause_chain_split.evalClause_congr a a' C
        (fun l hl => heval_lt l.2 (hN C hCN l hl))]
      exact ha C (List.mem_cons_of_mem _ hCN)
