import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

namespace PvsNP.Units.m3_y_xor_path_models_count

private lemma sublist_eq_of_mem_iff :
    ∀ {l a b : List ℕ}, l.Nodup → List.Sublist a l → List.Sublist b l → (∀ x, x ∈ a ↔ x ∈ b) → a = b
  | [], a, b, _, ha, hb, _ => by
    rw [List.sublist_nil.mp ha, List.sublist_nil.mp hb]
  | y :: l, a, b, hnd, ha, hb, hmem => by
    rw [List.nodup_cons] at hnd
    cases ha with
    | cons _ ha' =>
      have hya : y ∉ a := fun h => hnd.1 (ha'.subset h)
      cases hb with
      | cons _ hb' => exact sublist_eq_of_mem_iff hnd.2 ha' hb' hmem
      | cons_cons _ hb' => exact absurd ((hmem y).mpr List.mem_cons_self) hya
    | cons_cons _ ha' =>
      rename_i a'
      cases hb with
      | cons _ hb' =>
        have hyb : y ∉ b := fun h => hnd.1 (hb'.subset h)
        exact absurd ((hmem y).mp List.mem_cons_self) hyb
      | cons_cons _ hb' =>
        rename_i b'
        congr 1
        apply sublist_eq_of_mem_iff hnd.2 ha' hb'
        intro x
        by_cases h : x = y
        · subst h
          exact ⟨fun hx => absurd (ha'.subset hx) hnd.1, fun hx => absurd (hb'.subset hx) hnd.1⟩
        · have := hmem x
          simpa [List.mem_cons, h] using this

private lemma evalCnf_xorPath_iff (n : ℕ) (a : assgn) :
    evalCnf a ((List.range n).flatMap
        (fun i => [[(true, i), (true, i + 1)], [(false, i), (false, i + 1)]])) = true ↔
      ∀ i < n, (i + 1 ∈ a ↔ i ∉ a) := by
  rw [evalCnf_clause_iff]
  constructor
  · intro h i hi
    have h1 : evalClause a [(true, i), (true, i + 1)] = true := by
      apply h
      rw [List.mem_flatMap]
      exact ⟨i, List.mem_range.mpr hi, by simp⟩
    have h2 : evalClause a [(false, i), (false, i + 1)] = true := by
      apply h
      rw [List.mem_flatMap]
      exact ⟨i, List.mem_range.mpr hi, by simp⟩
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
      evalLiteral, evalVar, decide_eq_true_eq] at h1 h2
    by_cases hi_mem : i ∈ a <;> by_cases hi1_mem : i + 1 ∈ a <;> simp_all
  · intro h C hC
    rw [List.mem_flatMap] at hC
    obtain ⟨i, hi_mem, hCi⟩ := hC
    have hi : i < n := List.mem_range.mp hi_mem
    have halt := h i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hCi
    rcases hCi with rfl | rfl
    · simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
        evalLiteral, evalVar, decide_eq_true_eq]
      by_cases hmem : i ∈ a
      · exact Or.inl (by simp [hmem])
      · exact Or.inr (by simp [halt.mpr hmem])
    · simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
        evalLiteral, evalVar]
      by_cases hmem : i ∈ a
      · exact Or.inr (by
          have hnot : i + 1 ∉ a := fun h1 => (halt.mp h1) hmem
          simp [hnot])
      · exact Or.inl (by simp [hmem])

private lemma alt_mem_even {n : ℕ} {a : List ℕ}
    (halt : ∀ i < n, (i + 1 ∈ a ↔ i ∉ a)) (h0 : 0 ∈ a) :
    ∀ i ≤ n, (i ∈ a ↔ i % 2 = 0) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [h0]
  | succ i ih =>
    intro hi
    have hlt : i < n := by omega
    rw [halt i hlt, ih (by omega)]
    omega

private lemma alt_mem_odd {n : ℕ} {a : List ℕ}
    (halt : ∀ i < n, (i + 1 ∈ a ↔ i ∉ a)) (h0 : 0 ∉ a) :
    ∀ i ≤ n, (i ∈ a ↔ i % 2 = 1) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp [h0]
  | succ i ih =>
    intro hi
    have hlt : i < n := by omega
    rw [halt i hlt, ih (by omega)]
    omega

end PvsNP.Units.m3_y_xor_path_models_count

/-- Over the variables `0, …, n`, the inequality path `x₀ ≠ x₁ ≠ … ≠ x_n` has exactly two models
(vendored model). -/
theorem PvsNP.Units.m3_y_xor_path_models_count :
    ∀ n : ℕ,
      ((List.range (n + 1)).sublists.filter (fun a =>
        evalCnf a ((List.range n).flatMap
          (fun i => [[(true, i), (true, i + 1)], [(false, i), (false, i + 1)]])))).length = 2 := by
  intro n
  classical
  let N : cnf := (List.range n).flatMap
    (fun i => [[(true, i), (true, i + 1)], [(false, i), (false, i + 1)]])
  let S : List (List ℕ) := (List.range (n + 1)).sublists.filter (fun a => evalCnf a N)
  have hS_nd : S.Nodup := (List.nodup_sublists.mpr List.nodup_range).filter _
  let evens : List ℕ := (List.range (n + 1)).filter (fun i => decide (i % 2 = 0))
  let odds : List ℕ := (List.range (n + 1)).filter (fun i => decide (i % 2 = 1))
  have hne : evens ≠ odds := by
    intro heq
    have h0e : 0 ∈ evens := by simp [evens]
    rw [heq] at h0e
    simp [odds] at h0e
  have hset : S.toFinset = {evens, odds} := by
    ext a
    simp only [S, List.mem_toFinset, List.mem_filter, List.mem_sublists,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, heval⟩
      have halt := (PvsNP.Units.m3_y_xor_path_models_count.evalCnf_xorPath_iff n a).mp heval
      by_cases h0 : 0 ∈ a
      · left
        have hmem := PvsNP.Units.m3_y_xor_path_models_count.alt_mem_even halt h0
        apply PvsNP.Units.m3_y_xor_path_models_count.sublist_eq_of_mem_iff
          List.nodup_range hsub List.filter_sublist
        intro x
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        constructor
        · intro hx
          have hxlt : x < n + 1 := List.mem_range.mp (hsub.subset hx)
          exact ⟨hxlt, (hmem x (by omega)).mp hx⟩
        · rintro ⟨hxlt, hxmod⟩
          exact (hmem x (by omega)).mpr hxmod
      · right
        have hmem := PvsNP.Units.m3_y_xor_path_models_count.alt_mem_odd halt h0
        apply PvsNP.Units.m3_y_xor_path_models_count.sublist_eq_of_mem_iff
          List.nodup_range hsub List.filter_sublist
        intro x
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        constructor
        · intro hx
          have hxlt : x < n + 1 := List.mem_range.mp (hsub.subset hx)
          exact ⟨hxlt, (hmem x (by omega)).mp hx⟩
        · rintro ⟨hxlt, hxmod⟩
          exact (hmem x (by omega)).mpr hxmod
    · rintro (rfl | rfl)
      · refine ⟨List.filter_sublist, ?_⟩
        rw [PvsNP.Units.m3_y_xor_path_models_count.evalCnf_xorPath_iff]
        intro i hi
        simp only [evens, List.mem_filter, List.mem_range, decide_eq_true_eq]
        omega
      · refine ⟨List.filter_sublist, ?_⟩
        rw [PvsNP.Units.m3_y_xor_path_models_count.evalCnf_xorPath_iff]
        intro i hi
        simp only [odds, List.mem_filter, List.mem_range, decide_eq_true_eq]
        omega
  calc S.length
      = S.toFinset.card := (List.toFinset_card_of_nodup hS_nd).symm
    _ = ({evens, odds} : Finset (List ℕ)).card := by rw [hset]
    _ = 2 := Finset.card_pair hne
