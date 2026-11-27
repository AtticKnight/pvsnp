import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_ite_polytime
import PvsNP.Units.m2_const_polytime

/-
A language in P reduces to a nontrivial language by a map with only two
values (TM2).

Proof: take the polynomial-time decider `d` of `L₁` (the definition of P) and
set `f x = if d x = true then a else b`. The map is polynomial-time by the
settled unit `m2_ite_polytime` with both branches constant (the settled unit
`m2_const_polytime`); it takes only the values `a` and `b`, and
`x ∈ L₁ ↔ d x = true ↔ f x ∈ L₂` since `a ∈ L₂` and `b ∉ L₂`.
-/

set_option autoImplicit false

namespace PvsNP.Units.m2_p_reduces_two_values

theorem main : ∀ (L₁ L₂ : Language Bool) (a b : List Bool), L₁ ∈ PvsNP.P → a ∈ L₂ → b ∉ L₂ →
  ∃ f : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f ∧
    (∀ x : List Bool, f x = a ∨ f x = b) ∧ ∀ x : List Bool, x ∈ L₁ ↔ f x ∈ L₂ := by
  intro L₁ L₂ a b hL₁ ha hb
  obtain ⟨d, hd, hdec⟩ := hL₁
  refine ⟨fun x => if d x = true then a else b, ?_, ?_, ?_⟩
  · exact PvsNP.Units.m2_ite_polytime d (fun _ => a) (fun _ => b) hd
      (PvsNP.Units.m2_const_polytime a) (PvsNP.Units.m2_const_polytime b)
  · intro x
    by_cases h : d x = true <;> simp [h]
  · intro x
    rw [hdec x]
    by_cases h : d x = true <;> simp [h, ha, hb]

end PvsNP.Units.m2_p_reduces_two_values

/-- A language in P reduces to a nontrivial language by a map with only two values (TM2). -/
theorem PvsNP.Units.m2_p_reduces_two_values : ∀ (L₁ L₂ : Language Bool) (a b : List Bool), L₁ ∈ PvsNP.P → a ∈ L₂ → b ∉ L₂ →
  ∃ f : List Bool → List Bool, PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString f ∧
    (∀ x : List Bool, f x = a ∨ f x = b) ∧ ∀ x : List Bool, x ∈ L₁ ↔ f x ∈ L₂ :=
  PvsNP.Units.m2_p_reduces_two_values.main
