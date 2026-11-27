import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_reverse_polytime

theorem PvsNP.Units.m2_x_composite_endian_karp_equiv :
    PvsNP.KarpReducible ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool)
    ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.reverse.map Bool.toNat)} : Language Bool) ∧
  PvsNP.KarpReducible ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.reverse.map Bool.toNat)} : Language Bool)
    ({x : List Bool | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (x.map Bool.toNat)} : Language Bool) := by
  constructor
  · refine ⟨List.reverse, PvsNP.Units.m2_reverse_polytime, fun x => ?_⟩
    let C := fun z : List Bool => ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = Nat.ofDigits (2 : ℕ) (z.map Bool.toNat)
    change C x ↔ C x.reverse.reverse
    rw [List.reverse_reverse]
  · exact ⟨List.reverse, PvsNP.Units.m2_reverse_polytime, fun _ => Iff.rfl⟩
