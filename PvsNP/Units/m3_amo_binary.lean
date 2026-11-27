import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_amo_binary_aux

theorem eq_of_testBit_lt {m x y : ℕ} (hx : x < 2 ^ m) (hy : y < 2 ^ m)
    (h : ∀ j : ℕ, j < m → Nat.testBit x j = Nat.testBit y j) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < m
  · exact h j hj
  · have hm : m ≤ j := by omega
    have hpow : 2 ^ m ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hm
    have hx' : Nat.testBit x j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hpow)
    have hy' : Nat.testBit y j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hpow)
    rw [hx', hy']

theorem length_le_one_of_nodup_eq {α : Type} {l : List α} (hn : l.Nodup)
    (heq : ∀ x ∈ l, ∀ y ∈ l, x = y) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys =>
      exfalso
      have hxy : x = y := heq x (List.mem_cons.mpr (Or.inl rfl))
        y (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      have hxnot : x ∉ y :: ys := (List.nodup_cons.mp hn).1
      exact hxnot (List.mem_cons.mpr (Or.inl hxy))

theorem amo_forward (n m : ℕ) (a : assgn) (hm : n ≤ 2 ^ m)
    (h : ∃ b : assgn, (∀ i < n, (i ∈ b ↔ i ∈ a)) ∧
      satisfiesCnf b ((List.range n).flatMap (fun i =>
        (List.range m).map (fun j => [(false, i), (Nat.testBit i j, n + j)])))) :
    ((List.range n).filter (fun i => decide (i ∈ a))).length ≤ 1 := by
  obtain ⟨b, hba, hsat⟩ := h
  have hnodup : ((List.range n).filter (fun i => decide (i ∈ a))).Nodup :=
    List.Nodup.sublist List.filter_sublist List.nodup_range
  refine length_le_one_of_nodup_eq hnodup ?_
  intro x hx y hy
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hx hy
  have hxb : x ∈ b := (hba x hx.1).mpr hx.2
  have hyb : y ∈ b := (hba y hy.1).mpr hy.2
  have hcnf : ∀ C ∈ (List.range n).flatMap (fun i =>
      (List.range m).map (fun j => [(false, i), (Nat.testBit i j, n + j)])),
      evalClause b C = true :=
    (evalCnf_clause_iff b _).mp hsat
  refine eq_of_testBit_lt (lt_of_lt_of_le hx.1 hm) (lt_of_lt_of_le hy.1 hm) (fun j hj => ?_)
  have bit_eq : ∀ i, i < n → i ∈ b → Nat.testBit i j = evalVar b (n + j) := by
    intro i hi hib
    have hmem : [(false, i), (Nat.testBit i j, n + j)] ∈
        (List.range n).flatMap (fun i =>
          (List.range m).map (fun j => [(false, i), (Nat.testBit i j, n + j)])) :=
      List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
        List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩
    have hc := (evalClause_literal_iff b _).mp (hcnf _ hmem)
    rcases hc with ⟨l, hl, hlit⟩
    rcases List.mem_cons.mp hl with rfl | hl'
    · simp only [evalLiteral, evalVar, decide_eq_true_eq] at hlit
      have hnot : i ∉ b := by simpa using hlit
      exact absurd hib hnot
    · rcases List.mem_singleton.mp hl' with rfl
      simp only [evalLiteral, decide_eq_true_eq] at hlit
      exact hlit.symm
  rw [bit_eq x hx.1 hxb, bit_eq y hy.1 hyb]

theorem mem_ext_iff (n m k x : ℕ) (hk : k < n) :
    x ∈ k :: (List.range m).filterMap
      (fun j => if Nat.testBit k j then some (n + j) else none) →
    (x < n → x = k) := by
  intro hx hxn
  rcases List.mem_cons.mp hx with rfl | hmem
  · rfl
  · rw [List.mem_filterMap] at hmem
    rcases hmem with ⟨j, _, hj⟩
    by_cases hbit : Nat.testBit k j
    · simp only [hbit, ↓reduceIte] at hj
      have := Option.some.inj hj
      omega
    · simp only [hbit, Bool.false_eq_true, ↓reduceIte] at hj
      cases hj

theorem amo_backward (n m : ℕ) (a : assgn)
    (hlen : ((List.range n).filter (fun i => decide (i ∈ a))).length ≤ 1) :
    ∃ b : assgn, (∀ i < n, (i ∈ b ↔ i ∈ a)) ∧
      satisfiesCnf b ((List.range n).flatMap (fun i =>
        (List.range m).map (fun j => [(false, i), (Nat.testBit i j, n + j)]))) := by
  cases hS : (List.range n).filter (fun i => decide (i ∈ a)) with
  | nil =>
    refine ⟨[], fun i hi => ?_, ?_⟩
    · constructor
      · intro hmem; cases hmem
      · intro hmem
        exfalso
        have hmemS : i ∈ (List.range n).filter (fun i => decide (i ∈ a)) :=
          List.mem_filter.mpr ⟨List.mem_range.mpr hi, decide_eq_true_eq.mpr hmem⟩
        rw [hS] at hmemS
        cases hmemS
    · rw [satisfiesCnf, evalCnf_clause_iff]
      intro C hC
      rw [List.mem_flatMap] at hC
      rcases hC with ⟨i, _, hCi⟩
      rw [List.mem_map] at hCi
      rcases hCi with ⟨j, _, rfl⟩
      rw [evalClause_literal_iff]
      refine ⟨(false, i), List.mem_cons.mpr (Or.inl rfl), ?_⟩
      simp [evalLiteral, evalVar]
  | cons k rest =>
    cases rest with
    | cons _ _ =>
      rw [hS] at hlen
      simp at hlen
    | nil =>
      have hkS : k ∈ (List.range n).filter (fun i => decide (i ∈ a)) := by
        rw [hS]; exact List.mem_cons.mpr (Or.inl rfl)
      rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hkS
      let ext : List var := (List.range m).filterMap
        (fun j => if Nat.testBit k j then some (n + j) else none)
      refine ⟨k :: ext, fun i hi => ?_, ?_⟩
      · constructor
        · intro hib
          have hik : i = k := mem_ext_iff n m k i hkS.1 hib hi
          rw [hik]
          exact hkS.2
        · intro hia
          have hiS : i ∈ (List.range n).filter (fun i => decide (i ∈ a)) :=
            List.mem_filter.mpr ⟨List.mem_range.mpr hi, decide_eq_true_eq.mpr hia⟩
          rw [hS, List.mem_singleton] at hiS
          rw [hiS]
          exact List.mem_cons.mpr (Or.inl rfl)
      · rw [satisfiesCnf, evalCnf_clause_iff]
        intro C hC
        rw [List.mem_flatMap] at hC
        rcases hC with ⟨i, hi, hCi⟩
        rw [List.mem_range] at hi
        rw [List.mem_map] at hCi
        rcases hCi with ⟨j, hj, rfl⟩
        rw [List.mem_range] at hj
        rw [evalClause_literal_iff]
        by_cases hik : i = k
        · rw [hik]
          refine ⟨(Nat.testBit k j, n + j),
            List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)), ?_⟩
          have hext : n + j ∈ ext ↔ Nat.testBit k j = true := by
            simp only [ext, List.mem_filterMap, List.mem_range]
            constructor
            · rintro ⟨j', _, hite⟩
              by_cases hbit : Nat.testBit k j' = true
              · rw [if_pos hbit] at hite
                have hsum : n + j' = n + j := Option.some.inj hite
                have hj' : j' = j := by omega
                rw [← hj']
                exact hbit
              · rw [if_neg hbit] at hite
                cases hite
            · intro hbit
              refine ⟨j, hj, ?_⟩
              rw [if_pos hbit]
          have hmem_b : n + j ∈ k :: ext ↔ Nat.testBit k j = true := by
            rw [List.mem_cons]
            constructor
            · rintro (hne | hmem)
              · omega
              · exact hext.mp hmem
            · intro hbit
              exact Or.inr (hext.mpr hbit)
          have heval : evalVar (k :: ext) (n + j) = Nat.testBit k j := by
            apply Bool.eq_iff_iff.mpr
            simp only [evalVar, decide_eq_true_eq]
            exact hmem_b
          rw [evalLiteral, heval]
          simp
        · refine ⟨(false, i), List.mem_cons.mpr (Or.inl rfl), ?_⟩
          have hinotb : i ∉ k :: ext := by
            intro hmem
            exact hik (mem_ext_iff n m k i hkS.1 hmem hi)
          simp [evalLiteral, evalVar, hinotb]

end PvsNP.Units.m3_amo_binary_aux

theorem PvsNP.Units.m3_amo_binary :
    ∀ (n m : ℕ) (a : assgn), n ≤ 2 ^ m →
      ((∃ b : assgn, (∀ i < n, (i ∈ b ↔ i ∈ a)) ∧
        satisfiesCnf b ((List.range n).flatMap (fun i =>
          (List.range m).map (fun j => [(false, i), (Nat.testBit i j, n + j)])))) ↔
        ((List.range n).filter (fun i => decide (i ∈ a))).length ≤ 1) := by
  intro n m a hm
  exact ⟨PvsNP.Units.m3_amo_binary_aux.amo_forward n m a hm,
    PvsNP.Units.m3_amo_binary_aux.amo_backward n m a⟩
