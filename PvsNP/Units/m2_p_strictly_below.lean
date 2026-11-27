import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_p_trivial
import PvsNP.Units.m2_p_reduces_nontrivial
import PvsNP.Units.m2_p_down_closed

/-
Closes m2_p_strictly_below: any language outside P is neither empty nor
universal (`m2_p_trivial`), so every language in P Karp-reduces to it
(`m2_p_reduces_nontrivial`); conversely, it cannot Karp-reduce to a language
in P because P is downward closed under Karp reductions (`m2_p_down_closed`).
-/

set_option autoImplicit false

/-- Every nontrivial language in P lies strictly below every language outside P (TM2). -/
theorem PvsNP.Units.m2_p_strictly_below :
    ∀ L₀ L : Language Bool, L₀ ∈ PvsNP.P → (∃ y : List Bool, y ∈ L₀) → (∃ z : List Bool, z ∉ L₀) →
      L ∉ PvsNP.P → PvsNP.KarpReducible L₀ L ∧ ¬ PvsNP.KarpReducible L L₀ := by
  intro L₀ L hL₀ _ _ hLnP
  have hyL : ∃ y : List Bool, y ∈ L := by
    by_contra h
    have hEq : L = (∅ : Set (List Bool)) := Set.ext fun x =>
      ⟨fun hx => absurd ⟨x, hx⟩ h, fun hx => (hx : False).elim⟩
    rw [hEq] at hLnP
    exact hLnP PvsNP.Units.m2_p_trivial.1
  have hzL : ∃ z : List Bool, z ∉ L := by
    by_contra h
    have hEq : L = (Set.univ : Set (List Bool)) := Set.ext fun x =>
      ⟨fun _ => trivial, fun _ => by by_contra hnx; exact h ⟨x, hnx⟩⟩
    rw [hEq] at hLnP
    exact hLnP PvsNP.Units.m2_p_trivial.2
  exact ⟨PvsNP.Units.m2_p_reduces_nontrivial L₀ L hL₀ hyL hzL,
    fun hred => hLnP (PvsNP.Units.m2_p_down_closed L L₀ hred hL₀)⟩
