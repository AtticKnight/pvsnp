import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_tovey

open Classical

theorem card_filter_get {α : Type} (l : List α) (p : α → Bool) :
    ((Finset.univ : Finset (Fin l.length)).filter (fun i => p (l.get i) = true)).card =
      l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [Finset.card_filter]
    refine (Fin.sum_univ_succ (n := l.length)
      (fun i => if p ((a :: l).get i) = true then 1 else 0)).trans ?_
    rw [Finset.card_filter] at ih
    show (if p a = true then 1 else 0) +
        ∑ i : Fin l.length, (if p (l.get i) = true then 1 else 0) = _
    rw [ih, List.countP_cons]
    cases p a <;> simp; omega

def tv (N : cnf) (i : Fin N.length) : Finset var := ((N.get i).map Prod.snd).toFinset

theorem hall (k : ℕ) (N : cnf) (hk : 0 < k)
    (hC : ∀ C ∈ N, k ≤ C.length ∧ (C.map Prod.snd).Nodup)
    (hv : ∀ v : var, (N.filter (fun C => decide (∃ l ∈ C, l.2 = v))).length ≤ k)
    (s : Finset (Fin N.length)) : s.card ≤ (s.biUnion (tv N)).card := by
  set U := s.biUnion (tv N) with hU
  have hcard : ∀ i : Fin N.length, k ≤ (tv N i).card := by
    intro i
    have h := hC (N.get i) (List.get_mem N i)
    unfold tv
    rw [List.toFinset_card_of_nodup h.2, List.length_map]
    exact h.1
  have hcol : ∀ v : var, (s.filter (fun i => v ∈ tv N i)).card ≤ k := by
    intro v
    have h1 : (s.filter (fun i => v ∈ tv N i)).card ≤
        ((Finset.univ : Finset (Fin N.length)).filter
          (fun i => (fun C : clause => decide (∃ l ∈ C, l.2 = v)) (N.get i) = true)).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      have := hi.2
      unfold tv at this
      simp only [List.mem_toFinset, List.mem_map] at this
      obtain ⟨l, hl, hl2⟩ := this
      exact ⟨l, hl, hl2⟩
    have h2 := card_filter_get N (fun C : clause => decide (∃ l ∈ C, l.2 = v))
    rw [List.countP_eq_length_filter] at h2
    exact (le_of_le_of_eq h1 h2).trans (hv v)
  have hsum1 : k * s.card ≤ ∑ i ∈ s, (tv N i).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun i _ => hcard i)
  have hsum2 : ∑ i ∈ s, (tv N i).card = ∑ v ∈ U, (s.filter (fun i => v ∈ tv N i)).card := by
    have e : ∀ i ∈ s, (tv N i).card = ∑ v ∈ U, (if v ∈ tv N i then 1 else 0) := by
      intro i hi
      rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter]
      congr 1
      symm
      apply Finset.inter_eq_right.mpr
      intro v hv
      rw [hU, Finset.mem_biUnion]
      exact ⟨i, hi, hv⟩
    rw [Finset.sum_congr rfl e, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_boole, Nat.cast_id]
  have hsum3 : ∑ v ∈ U, (s.filter (fun i => v ∈ tv N i)).card ≤ U.card * k := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun v _ => hcol v)
  have : k * s.card ≤ k * U.card := by
    calc k * s.card ≤ _ := hsum1
      _ = _ := hsum2
      _ ≤ U.card * k := hsum3
      _ = k * U.card := mul_comm _ _
  exact Nat.le_of_mul_le_mul_left this hk

end PvsNP.Units.m3_tovey

open PvsNP.Units.m3_tovey in
theorem PvsNP.Units.m3_tovey :
    ∀ (k : ℕ) (N : cnf), 0 < k →
      (∀ C ∈ N, k ≤ C.length ∧ (C.map Prod.snd).Nodup) →
        (∀ v : var, (N.filter (fun C => decide (∃ l ∈ C, l.2 = v))).length ≤ k) →
          SAT N := by
  classical
  intro k N hk hC hv
  obtain ⟨f, hinj, hf⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (tv N)).mp (hall k N hk hC hv)
  have hex : ∀ i : Fin N.length, ∃ l : literal, l ∈ N.get i ∧ l.2 = f i := by
    intro i
    have := hf i
    unfold tv at this
    simp only [List.mem_toFinset, List.mem_map] at this
    exact this
  choose g hg1 hg2 using hex
  let a : assgn := (((Finset.univ : Finset (Fin N.length)).filter (fun i => (g i).1 = true)).image f).toList
  have hev : ∀ i, evalVar a (f i) = (g i).1 := by
    intro i
    unfold evalVar
    by_cases h : (g i).1 = true
    · rw [h]
      simp only [decide_eq_true_eq, a, Finset.mem_toList, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨i, h, rfl⟩
    · have h' : (g i).1 = false := by simpa using h
      rw [h']
      simp only [decide_eq_false_iff_not, a, Finset.mem_toList, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, not_exists, not_and]
      intro j hj hfj
      rw [hinj hfj] at hj
      exact h hj
  refine ⟨a, ?_⟩
  unfold satisfiesCnf evalCnf
  rw [List.all_eq_true]
  intro C hCN
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hCN
  rw [evalClause_literal_iff]
  refine ⟨g i, hg1 i, ?_⟩
  have h := hev i
  rw [← hg2 i] at h
  revert h
  generalize g i = l
  obtain ⟨sgn, v⟩ := l
  intro h
  simp only [evalLiteral, decide_eq_true_eq]
  exact h
