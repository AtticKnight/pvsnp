import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m3_at_least_k_binomial

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

end PvsNP.Units.m3_at_least_k_binomial

theorem PvsNP.Units.m3_at_least_k_binomial :
    ∀ (vs : List var) (k : ℕ) (a : assgn),
  evalCnf a ((vs.sublistsLen (vs.length + 1 - k)).map (fun s => s.map (fun v => (true, v)))) = true ↔
    k ≤ (vs.filter (fun v => decide (v ∈ a))).length := by
  intro vs k a
  have key := PvsNP.Units.m3_at_least_k_binomial.exists_sub_iff vs
    (fun v => !decide (v ∈ a)) (vs.length + 1 - k)
  have hlen : vs.length = (vs.filter (fun v => decide (v ∈ a))).length +
      (vs.filter (fun v => !decide (v ∈ a))).length :=
    List.length_eq_length_filter_add _
  rw [evalCnf_clause_iff]
  constructor
  · intro h
    by_contra hk
    have hle : vs.length + 1 - k ≤ (vs.filter (fun v => !decide (v ∈ a))).length := by omega
    obtain ⟨s, hs, hq⟩ := key.mpr hle
    have hc := h _ (List.mem_map.mpr ⟨s, hs, rfl⟩)
    rw [evalClause_literal_iff] at hc
    obtain ⟨l, hl, he⟩ := hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
    have h1 : v ∈ a := by simpa [evalLiteral, evalVar] using he
    have h2 : v ∉ a := by simpa using hq v hv
    exact h2 h1
  · intro hk C hC
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hC
    rw [evalClause_literal_iff]
    by_contra hne
    have hall : ∀ x ∈ s, (fun v => !decide (v ∈ a)) x = true := by
      intro x hx
      by_contra hx'
      apply hne
      refine ⟨(true, x), List.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
      simpa [evalLiteral, evalVar] using hx'
    have hge := key.mp ⟨s, hs, hall⟩
    omega
