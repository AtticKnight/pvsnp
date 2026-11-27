import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_pigeonhole

theorem exists_sub_iff {α : Type} (l : List α) (q : α → Bool) (m : ℕ) :
    (∃ s ∈ l.sublistsLen m, ∀ x ∈ s, q x = true) ↔ m ≤ (l.filter q).length := by
  constructor
  · rintro ⟨s, hs, hq⟩
    rw [List.mem_sublistsLen] at hs
    obtain ⟨hsub, hlen⟩ := hs
    have h1 : s.filter q = s := List.filter_eq_self.mpr hq
    have h2 : List.Sublist (s.filter q) (l.filter q) := hsub.filter q
    rw [h1] at h2
    rw [← hlen]
    exact h2.length_le
  · intro h
    refine ⟨(l.filter q).take m, ?_, ?_⟩
    · rw [List.mem_sublistsLen]
      refine ⟨(List.take_sublist _ _).trans List.filter_sublist, ?_⟩
      rw [List.length_take]
      exact min_eq_left h
    · intro x hx
      have hx' := List.mem_of_mem_take hx
      exact (List.mem_filter.mp hx').2

end PvsNP.Units.m3_pigeonhole

theorem PvsNP.Units.m3_pigeonhole :
    ∀ n : ℕ,
  ¬ SAT ((List.range (n + 1)).map (fun i => (List.range n).map (fun j => (true, i * n + j))) ++
    (List.range n).flatMap (fun j =>
      ((List.range (n + 1)).sublistsLen 2).map (fun p => p.map (fun i => (false, i * n + j))))) := by
  intro n hsat
  obtain ⟨a, ha⟩ := hsat
  unfold satisfiesCnf at ha
  rw [evalCnf_app_iff] at ha
  obtain ⟨h1, h2⟩ := ha
  rw [evalCnf_clause_iff] at h1 h2
  have hp : ∀ i, i < n + 1 → ∃ j, j < n ∧ i * n + j ∈ a := by
    intro i hi
    have hc := h1 _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    rw [evalClause_literal_iff] at hc
    obtain ⟨l, hl, he⟩ := hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    exact ⟨j, List.mem_range.mp hj, by simpa [evalLiteral, evalVar] using he⟩
  have hcol : ∀ j, j < n →
      ((List.range (n + 1)).filter (fun i => decide (i * n + j ∈ a))).length < 2 := by
    intro j hj
    by_contra hge
    obtain ⟨s, hs, hq⟩ :=
      (PvsNP.Units.m3_pigeonhole.exists_sub_iff (List.range (n + 1))
        (fun i => decide (i * n + j ∈ a)) 2).mpr (by omega)
    have hc := h2 (s.map (fun i => (false, i * n + j)))
      (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_map.mpr ⟨s, hs, rfl⟩⟩)
    rw [evalClause_literal_iff] at hc
    obtain ⟨l, hl, he⟩ := hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    have hn1 : i * n + j ∉ a := by simpa [evalLiteral, evalVar] using he
    have hn2 : i * n + j ∈ a := by simpa using hq i hi
    exact hn1 hn2
  choose! g hg using hp
  obtain ⟨x, hx, y, hy, hxy, hfe⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := Finset.range (n + 1))
      (t := Finset.range n) (f := g) (by simp) (by
        intro i hi
        simp only [Finset.mem_coe, Finset.mem_range] at hi ⊢
        exact (hg i hi).1)
  simp only [Finset.mem_range] at hx hy
  have hc2 := hcol (g x) (hg x hx).1
  have hsub : [x, y] ⊆ (List.range (n + 1)).filter (fun i => decide (i * n + g x ∈ a)) := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hx, (hg _ hx).2⟩
    · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      rw [hfe]
      exact ⟨hy, (hg _ hy).2⟩
  have hnd : [x, y].Nodup := by simp [hxy]
  have hle := (List.subperm_of_subset hnd hsub).length_le
  simp only [List.length_cons, List.length_nil] at hle
  omega
