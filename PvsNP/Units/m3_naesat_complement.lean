import Mathlib
import PvsNP.Defs
import CookLevin

set_option autoImplicit false

theorem PvsNP.Units.m3_naesat_complement :
    ∀ (n : ℕ) (N : cnf) (a : assgn), (∀ C ∈ N, ∀ l ∈ C, l.2 < n) →
      (∀ C ∈ N, C.any (evalLiteral a) = true ∧ C.any (fun l => !evalLiteral a l) = true) →
        ∀ C ∈ N, C.any (evalLiteral ((List.range n).filter (fun v => decide (v ∉ a)))) = true ∧
          C.any (fun l => !evalLiteral ((List.range n).filter (fun v => decide (v ∉ a))) l) = true := by
  intro n N a hv hN C hC
  have _hc := Classical.em True
  have key : ∀ l ∈ C, evalLiteral ((List.range n).filter (fun v => decide (v ∉ a))) l =
      !evalLiteral a l := by
    rintro ⟨s, v⟩ hl
    have hvn : v < n := hv C hC _ hl
    cases s <;> by_cases hva : v ∈ a <;> simp [evalLiteral, evalVar, hva, hvn]
  obtain ⟨h1, h2⟩ := hN C hC
  rw [List.any_eq_true] at h1 h2
  constructor
  · rw [List.any_eq_true]
    obtain ⟨l, hl, hl'⟩ := h2
    exact ⟨l, hl, by rw [key l hl]; exact hl'⟩
  · rw [List.any_eq_true]
    obtain ⟨l, hl, hl'⟩ := h1
    exact ⟨l, hl, by rw [key l hl]; simpa using hl'⟩
