import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_exp_down_closed
import PvsNP.Units.m2_reverse_polytime
import PvsNP.Units.m2_inv_hom_closed

set_option autoImplicit false

/-- EXP is closed under reversal and inverse homomorphisms: both inverse images reduce to the
original language by polynomial-time computable maps, and EXP is downward closed. -/
theorem PvsNP.Units.m2_exp_reverse_inv_hom :
    ∀ (h : Bool → List Bool) (L : Language Bool),
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
      (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ ({x : List Bool | x.reverse ∈ L} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) ∧
        ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
            (∀ x : List Bool, x ∈ ({x : List Bool | x.flatMap h ∈ L} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro h L hExp
  constructor
  · exact PvsNP.Units.m2_exp_down_closed ({x : List Bool | x.reverse ∈ L} : Language Bool) L
      ⟨fun x : List Bool => x.reverse, PvsNP.Units.m2_reverse_polytime, fun _ => Iff.rfl⟩ hExp
  · exact PvsNP.Units.m2_exp_down_closed ({x : List Bool | x.flatMap h ∈ L} : Language Bool) L
      ⟨fun x : List Bool => x.flatMap h, PvsNP.Units.m2_inv_hom_closed.cpt_flatMap h, fun _ => Iff.rfl⟩ hExp
